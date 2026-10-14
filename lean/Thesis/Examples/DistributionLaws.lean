import Thesis.Probability.Distros

namespace Thesis.Examples.DistributionLaws

open Probability Probability.Distros

/-!
Executable kernel-checked regressions for the named finite distribution
laws.  Use `decide`, not `native_decide`, so the normal axiom gate also
checks these concrete evaluations.
-/

/-- The half-base Gaussian decreases away from its centre. -/
example :
    QProb.Equiv
      ((discreteGaussianDistro 2 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])).pmf ⟨2, by decide⟩)
      ⟨16, 34, by decide⟩ := by decide

example :
    QProb.Equiv
      ((discreteGaussianDistro 2 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])).pmf ⟨0, by decide⟩)
      ⟨1, 34, by decide⟩ := by decide

/-- A different presentation of the same rational base gives the same law. -/
example :
    QProb.Equiv
      ((discreteGaussianDistro 2 ⟨2, 4, by decide⟩ (by simp [QProb.LE, QProb.one])).pmf ⟨2, by decide⟩)
      ⟨16, 34, by decide⟩ := by decide

example :
    QProb.Equiv
      ((discreteGaussianDistro 3 QProb.zero (QProb.zero_le _)).pmf ⟨3, by decide⟩)
      QProb.one := by decide

example :
    QProb.Equiv
      ((discreteGaussianDistro 3 QProb.zero (QProb.zero_le _)).pmf ⟨0, by decide⟩)
      QProb.zero := by decide

example :
    QProb.Equiv
      ((discreteGaussianDistro 3 QProb.one (QProb.le_refl _)).pmf ⟨0, by decide⟩)
      ⟨1, 7, by decide⟩ := by decide

example :
    QProb.Equiv
      (mean (discreteGaussianNatDistro 0 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
      QProb.zero := by decide

/-- The zero-coordinate boundary remains the unit urn at zero. -/
example : QProb.Equiv (mean (chiSquaredDistro 0 2 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
    QProb.zero := by decide

/-- The squared coordinate uses the corrected Gaussian probabilities. -/
example : QProb.Equiv (mean (chiSquaredDistro 1 1 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
    ⟨1, 2, by decide⟩ := by decide

/-- Fair Bernoulli waiting time conditioned on success by the third trial. -/
example : QProb.Equiv ((geometricDistro 2 1 1 (by decide)).pmf ⟨0, by decide⟩)
    ⟨4, 7, by decide⟩ := by decide

example : QProb.Equiv ((geometricDistro 2 1 1 (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 7, by decide⟩ := by decide

/-- The same fair waiting time censored at two failures retains its tail. -/
example : QProb.Equiv ((geometricCensoredDistro 2 1 1 (by decide)).pmf ⟨0, by decide⟩)
    ⟨1, 2, by decide⟩ := by decide

example : QProb.Equiv ((geometricCensoredDistro 2 1 1 (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 4, by decide⟩ := by decide

/-- Scaling both trial weights preserves the Bernoulli parameter. -/
example : QProb.Equiv ((geometricDistro 2 2 2 (by decide)).pmf ⟨0, by decide⟩)
    ⟨4, 7, by decide⟩ := by decide

example : QProb.Equiv ((geometricCensoredDistro 2 2 2 (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 4, by decide⟩ := by decide

example : QProb.Equiv ((geometricCensoredDistro 0 1 1 (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

example : QProb.Equiv ((geometricDistro 3 2 0 (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

/-- Two successes: the censored occupancy denominator is four fair trials. -/
example : QProb.Equiv
    ((negativeBinomialDistro 2 2 1 1 (by decide) (by decide)).pmf ⟨0, by decide⟩)
    ⟨4, 11, by decide⟩ := by decide

example : QProb.Equiv
    ((negativeBinomialCensoredDistro 2 2 1 1 (by decide) (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 2, by decide⟩ := by decide

example : QProb.Equiv
    ((negativeBinomialCensoredDistro 2 2 2 2 (by decide) (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 2, by decide⟩ := by decide

example : QProb.Equiv
    ((negativeBinomialCensoredDistro 2 0 1 1 (by decide) (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

/-- A rational PGF argument must keep the original trial total fixed. -/
example : QProb.Equiv (pgf (geometricNatDistro 2 1 1 (by decide)) ⟨1, 2, by decide⟩)
    ⟨3, 4, by decide⟩ := by decide

example : QProb.Equiv (pgf (geometricCensoredNatDistro 2 1 1 (by decide)) ⟨1, 2, by decide⟩)
    ⟨11, 16, by decide⟩ := by decide

example : QProb.Equiv
    (pgf (negativeBinomialCensoredNatDistro 2 2 1 1 (by decide) (by decide)) ⟨1, 2, by decide⟩)
    ⟨1, 2, by decide⟩ := by decide

/-- The independent trial construction, including its no-success paths. -/
example : QProb.Equiv
    ((geometricCensoredFromBernoulli 2 1 1 (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 4, by decide⟩ := by decide

example : QProb.Equiv
    ((geometricCensoredFromBernoulli 0 1 1 (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

example : QProb.Equiv
    ((geometricFromBernoulli 2 1 1 (by decide)).pmf ⟨0, by decide⟩)
    ⟨4, 7, by decide⟩ := by decide

example : QProb.Equiv
    ((geometricFromBernoulli 2 2 2 (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 7, by decide⟩ := by decide

example : QProb.Equiv
    ((geometricFromBernoulli 0 1 1 (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

/-- Unequal trial weights exercise every denominator-clearing factor. -/
example :
    2 ^ 3 * Combinatorics.nbSumHomog 3 3 5 2 + negativeBinomialCensorTail 3 2 2 3 =
      5 ^ 5 := by decide

example : QProb.Equiv
    ((negativeBinomialFromBernoulli 3 2 2 3 (by decide) (by decide)).pmf ⟨0, by decide⟩)
    ⟨25, 124, by decide⟩ := by decide

example : QProb.Equiv
    ((negativeBinomialCensoredFromBernoulli 3 2 2 3 (by decide) (by decide)).pmf ⟨2, by decide⟩)
    ⟨513, 625, by decide⟩ := by decide

example : QProb.Equiv
    ((negativeBinomialCensoredFromBernoulli 2 2 1 1 (by decide) (by decide)).pmf ⟨2, by decide⟩)
    ⟨1, 2, by decide⟩ := by decide

example : QProb.Equiv
    ((negativeBinomialFromBernoulli 3 0 2 3 (by decide) (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

example : QProb.Equiv
    ((negativeBinomialCensoredFromBernoulli 3 2 2 0 (by decide) (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

/-- Unequal independent parameters exercise the generic moment and PGF laws. -/
example : QProb.Equiv
    (mean (independentSum (bernoulliNatDistro 2 3 (by decide))
      (bernoulliNatDistro 5 1 (by decide)))) ⟨37, 30, by decide⟩ := by decide

example : QProb.Equiv
    (variance (independentSum (bernoulliNatDistro 2 3 (by decide))
      (bernoulliNatDistro 5 1 (by decide)))) ⟨341, 900, by decide⟩ := by decide

example : QProb.Equiv
    (pgf (independentSum (bernoulliNatDistro 2 3 (by decide))
      (bernoulliNatDistro 5 1 (by decide))) ⟨1, 2, by decide⟩)
    ⟨7, 15, by decide⟩ := by decide

/-- Finite Gaussian moments differ from continuous Gaussian/χ² formulas. -/
example : QProb.Equiv
    (variance (discreteGaussianNatDistro 2 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
    ⟨12, 17, by decide⟩ := by decide

example : QProb.Equiv
    (mean (chiSquaredDistro 2 2 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
    ⟨24, 17, by decide⟩ := by decide

example : QProb.Equiv
    (variance (chiSquaredDistro 2 2 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
    ⟨528, 289, by decide⟩ := by decide

example : QProb.Equiv
    (variance (chiSquaredDistro 0 2 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
    QProb.zero := by decide

example : QProb.Equiv
    (variance (chiSquaredDistro 3 0 ⟨1, 2, by decide⟩ (by simp [QProb.LE, QProb.one])))
    QProb.zero := by decide

example : QProb.Equiv
    (variance (chiSquaredDistro 2 2 QProb.zero (QProb.zero_le _))) QProb.zero := by decide

/-- Reinforcement changes path weights; it does not give independent draws. -/
example : QProb.Equiv
    ((polyaPathRecord 3 2 3 (by decide)).probVal
      (FiniteProbRecord.singletonEvent [true, false, true])) ⟨3, 35, by decide⟩ := by decide

example : (betaBinomialDistro 3 2 3 (by decide) (by decide)).record.den = 210 := by decide

example : QProb.Equiv
    ((polyaUrnDistro 3 2 3 (by decide)).pmf ⟨2, by decide⟩)
    ⟨9, 35, by decide⟩ := by decide

example : QProb.Equiv
    ((betaBinomialDistro 3 2 3 (by decide) (by decide)).pmf ⟨2, by decide⟩)
    ⟨9, 35, by decide⟩ := by decide

example : QProb.Equiv (mean (betaBinomialNatDistro 3 2 3 (by decide) (by decide)))
    ⟨6, 5, by decide⟩ := by decide

example : QProb.Equiv
    ((polyaUrnDistro 0 2 3 (by decide)).pmf ⟨0, by decide⟩) QProb.one := by decide

example : QProb.Equiv
    ((polyaUrnDistro 3 0 2 (by decide)).pmf ⟨0, by decide⟩) QProb.one := by decide

/-- Multiple variables, mixed denominators, and an argument above one. -/
example : QProb.Equiv
    (multivariatePGF (multinomialDistro 2 [2, 3, 1] (by decide))
      [⟨1, 2, by decide⟩, QProb.ofNat 2, QProb.zero]) ⟨49, 36, by decide⟩ := by decide

example : QProb.Equiv
    (multivariatePGF (multinomialDistro 2 [2, 3, 1] (by decide))
      [⟨2, 4, by decide⟩, QProb.ofNat 2, QProb.zero]) ⟨49, 36, by decide⟩ := by decide

example : QProb.Equiv
    (multivariatePGF (multinomialDistro 2 [2, 3, 1] (by decide))
      ([1, 2, 3].map QProb.ofNat)) ⟨121, 36, by decide⟩ := by decide

example : QProb.Equiv
    (multivariatePGF (multinomialDistro 3 [0, 2] (by decide))
      [⟨17, 3, by decide⟩, ⟨1, 2, by decide⟩]) ⟨1, 8, by decide⟩ := by decide

example : QProb.Equiv
    (multivariatePGF (multinomialDistro 0 [2, 3, 1] (by decide))
      [QProb.zero, QProb.zero, QProb.zero]) QProb.one := by decide

example : QProb.Equiv (variance (bernoulliNatDistro 2 3 (by decide)))
    ⟨6, 25, by decide⟩ := by decide

example : QProb.Equiv (variance (binomialNatDistro 4 2 3 (by decide)))
    ⟨24, 25, by decide⟩ := by decide

example : QProb.Equiv (variance (binomialNatDistro 5 0 3 (by decide)))
    QProb.zero := by decide

example : QProb.Equiv (variance (binomialNatDistro 5 2 0 (by decide)))
    QProb.zero := by decide

example : QProb.Equiv (variance (binomialNatDistro 0 2 3 (by decide)))
    QProb.zero := by decide

example : QProb.Equiv (secondMoment (betaBinomialNatDistro 3 2 3 (by decide) (by decide)))
    ⟨12, 5, by decide⟩ := by decide

example : QProb.Equiv (variance (betaBinomialNatDistro 3 2 3 (by decide) (by decide)))
    ⟨24, 25, by decide⟩ := by decide

example : QProb.Equiv (variance (betaBinomialNatDistro 4 1 1 (by decide) (by decide)))
    (QProb.ofNat 2) := by decide

example : QProb.Equiv (variance (betaBinomialNatDistro 0 2 3 (by decide) (by decide)))
    QProb.zero := by decide

/-- Conditioning and censoring have different finite waiting-time moments. -/
example : QProb.Equiv (mean (geometricNatDistro 2 2 3 (by decide)))
    ⟨33, 49, by decide⟩ := by decide

example : QProb.Equiv (variance (geometricNatDistro 2 2 3 (by decide)))
    ⟨1410, 2401, by decide⟩ := by decide

example : QProb.Equiv (geometricVarianceClosed 2 2 3 (by decide))
    ⟨1410, 2401, by decide⟩ := by decide

example : QProb.Equiv (mean (geometricCensoredNatDistro 2 2 3 (by decide)))
    ⟨24, 25, by decide⟩ := by decide

example : QProb.Equiv (variance (geometricCensoredNatDistro 2 2 3 (by decide)))
    ⟨474, 625, by decide⟩ := by decide

example : QProb.Equiv (geometricCensoredVarianceClosed 2 2 3 (by decide))
    ⟨474, 625, by decide⟩ := by decide

example : QProb.Equiv (geometricVarianceClosed 0 2 3 (by decide)) QProb.zero := by decide

example : QProb.Equiv (geometricCensoredVarianceClosed 0 2 3 (by decide)) QProb.zero := by decide

example : QProb.Equiv (geometricVarianceClosed 3 2 0 (by decide)) QProb.zero := by decide

example : QProb.Equiv (geometricCensoredVarianceClosed 3 2 0 (by decide)) QProb.zero := by decide

end Thesis.Examples.DistributionLaws
