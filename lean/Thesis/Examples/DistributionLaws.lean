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

end Thesis.Examples.DistributionLaws
