import Thesis.Probability.Distros

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-! Boundary and presentation-invariance regressions for finite distro extensions. -/

/-- The ordinary mean-square deviation is invariant under rescaling the
Bernoulli weights, despite the integer squared-deviation numerator changing. -/
example (a b factor : Nat) (positive : 0 < b + a) (hfactor : 0 < factor) :
    QProb.Equiv
      (variance (⟨(bernoulliDistro a b positive).rescaleWeights factor hfactor,
        (bernoulliNatDistro a b positive).embed⟩ : NatDistro Bool))
      (variance (bernoulliNatDistro a b positive)) :=
  (NatDistro.sameLaw_of_distro
    ((bernoulliDistro a b positive).rescaleWeights_sameLaw factor hfactor)
    (bernoulliNatDistro a b positive).embed).variance

/-- Chebyshev includes the sharp boundary at radius one half for a fair bit. -/
example : QProb.LE
    ((bernoulliDistro 1 1 (by decide)).record.probVal (fun value => decide
      (1 * 1 * (2 * 2) ≤ sqDev (fun bit => if bit then 1 else 0) 1 2 value * (2 * 2))))
    (QProb.div (variance (bernoulliNatDistro 1 1 (by decide)))
      (QProb.mul ⟨1, 2, by decide⟩ ⟨1, 2, by decide⟩) (by decide)) :=
  chebyshev_rational (bernoulliNatDistro 1 1 (by decide)) ⟨1, 2, by decide⟩ (by decide)

example : QProb.Equiv (factorialMoment (binomialNatDistro 0 0 3 (by decide)) 0) QProb.one := by decide
example : QProb.Equiv (factorialMoment (binomialNatDistro 3 2 1 (by decide)) 4) QProb.zero := by decide
example : QProb.Equiv (factorialMoment (binomialNatDistro 5 2 3 (by decide)) 3)
    ⟨96, 25, by decide⟩ := by decide
example : QProb.Equiv (factorialMoment (betaBinomialNatDistro 5 2 3 (by decide) (by decide)) 3)
    ⟨48, 7, by decide⟩ := by decide
example : QProb.Equiv (factorialMoment (hypergeometricNatDistro 4 10 5 (by decide) (by decide)) 3)
    ⟨2, 1, by decide⟩ := by decide
example : QProb.Equiv (factorialMoment (hypergeometricNatDistro 0 0 0 (by decide) (by decide)) 0)
    QProb.one := by decide
example : QProb.Equiv (factorialMoment (hypergeometricNatDistro 0 0 0 (by decide) (by decide)) 1)
    QProb.zero := by decide

end Thesis.Examples.DistributionExtensions
