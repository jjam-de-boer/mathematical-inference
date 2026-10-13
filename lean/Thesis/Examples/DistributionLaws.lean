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

end Thesis.Examples.DistributionLaws
