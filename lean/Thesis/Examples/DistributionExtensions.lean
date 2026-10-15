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

/-- Reinforcement depends on observed counts, including the order-free
word probability and the actual conditioned next-draw record. -/
example : QProb.Equiv
    ((polyaPathRecord 3 2 3 (by decide)).probVal (FiniteProbRecord.singletonEvent [true, false, true]))
    ⟨3, 35, by decide⟩ := by decide
example : QProb.Equiv
    ((polyaPathRecord 3 2 3 (by decide)).probVal (FiniteProbRecord.singletonEvent [false, true, true]))
    ⟨3, 35, by decide⟩ := by decide
example : QProb.Equiv
    ((polyaContinuationDistro [true, true] 1 2 3 (by decide) (by decide)).record.probVal
      (FiniteProbRecord.singletonEvent [true]))
    ⟨4, 7, by decide⟩ := by decide
example : QProb.Equiv
    ((polyaContinuationDistro [false, false] 1 0 2 (by decide) (by decide)).record.probVal
      (FiniteProbRecord.singletonEvent [true]))
    QProb.zero := by decide

/-- Zero success weight censors every path at the cap. -/
example : QProb.Equiv ((geometricCensoredDistroOfTotal 4 0 2 (by decide)).pmf (Fin.last 4))
    QProb.one := by decide
example : QProb.Equiv (pgf (geometricCensoredNatDistroOfTotal 4 0 2 (by decide)) ⟨1, 2, by decide⟩)
    ⟨1, 16, by decide⟩ := by decide
example : QProb.Equiv ((negativeBinomialCensoredDistroOfTotal 3 4 0 2 (by decide) (by decide)).pmf (Fin.last 4))
    QProb.one := by decide
example : QProb.Equiv (variance (negativeBinomialCensoredNatDistroOfTotal 3 4 0 2 (by decide) (by decide)))
    QProb.zero := by decide
example : QProb.Equiv ((betaBinomialDistroOfTotal 5 0 3 (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide
example : QProb.Equiv ((betaBinomialDistroOfTotal 5 3 0 (by decide)).pmf (Fin.last 5))
    QProb.one := by decide
example : QProb.Equiv (mean (betaBinomialNatDistroOfTotal 5 3 0 (by decide)))
    (QProb.ofNat 5) := by decide
example : QProb.Equiv (factorialMoment (betaBinomialNatDistroOfTotal 5 3 0 (by decide)) 3)
    (QProb.ofNat 60) := by decide
example : QProb.Equiv (variance (betaBinomialNatDistroOfTotal 0 0 3 (by decide)))
    QProb.zero := by decide

/-- Several-success waiting times have finite-cap moments, distinct from
uncapped textbook formulas. -/
example : QProb.Equiv (negativeBinomialMeanClosed 3 4 2 3 (by decide))
    ⟨2547, 1133, by decide⟩ := by decide
example : QProb.Equiv (negativeBinomialVarianceClosed 3 4 2 3 (by decide) (by decide))
    ⟨2149650, 1283689, by decide⟩ := by decide
example : QProb.Equiv (negativeBinomialCensoredMeanClosed 3 4 2 3 (by decide))
    ⟨9324, 3125, by decide⟩ := by decide
example : QProb.Equiv (negativeBinomialCensoredVarianceClosed 3 4 2 3 (by decide) (by decide))
    ⟨16788024, 9765625, by decide⟩ := by decide
example : QProb.Equiv (negativeBinomialFactorialClosed 3 0 2 3 1 (by decide)) QProb.zero := by decide
example : QProb.Equiv (negativeBinomialFactorialClosed 3 2 2 3 3 (by decide)) QProb.zero := by decide
example : QProb.Equiv (negativeBinomialCensoredMeanClosed 3 4 0 2 (by decide))
    (QProb.ofNat 4) := by decide
example : QProb.Equiv (negativeBinomialCensoredVarianceClosed 3 4 0 2 (by decide) (by decide))
    QProb.zero := by decide

/-- Restricting a larger conditional window recovers the smaller law;
further censoring retains all mass in its last cell. -/
example : QProb.Equiv
    ((conditionFinCap (negativeBinomialDistro 3 5 2 3 (by decide) (by decide)) 2
      (negativeBinomial_cap_positive 3 2 5 2 3 (by decide) (by decide) (by decide))).pmf (Fin.last 2))
    ⟨27, 62, by decide⟩ := by decide
example : QProb.Equiv
    ((censorFinCap (negativeBinomialCensoredDistroOfTotal 3 5 2 3 (by decide) (by decide)) 2).pmf (Fin.last 2))
    ⟨513, 625, by decide⟩ := by decide
example : QProb.Equiv
    ((censorFinCap (negativeBinomialCensoredDistroOfTotal 3 5 0 2 (by decide) (by decide)) 2).pmf (Fin.last 2))
    QProb.one := by decide
example : QProb.Equiv
    ((conditionFinCap (negativeBinomialDistro 3 5 2 3 (by decide) (by decide)) 0
      (negativeBinomial_cap_positive 3 0 5 2 3 (by decide) (by decide) (by decide))).pmf ⟨0, by decide⟩)
    QProb.one := by decide

/-- The second same-colour draw uses a depleted urn, and reading off
counts gives hypergeometric even at the population boundaries. -/
example : QProb.Equiv
    ((depletingPathRecord 2 2 3 (by decide)).probVal (FiniteProbRecord.singletonEvent [true, true]))
    ⟨1, 10, by decide⟩ := by decide
example : QProb.Equiv ((hypergeometricFromUrn 2 5 3 (by decide) (by decide)).pmf ⟨1, by decide⟩)
    ⟨3, 5, by decide⟩ := by decide
example : QProb.Equiv ((hypergeometricFromUrn 2 5 5 (by decide) (by decide)).pmf ⟨2, by decide⟩)
    QProb.one := by decide
example : QProb.Equiv ((hypergeometricFromUrn 0 3 2 (by decide) (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide
example : QProb.Equiv ((hypergeometricFromUrn 3 3 2 (by decide) (by decide)).pmf (Fin.last 2))
    QProb.one := by decide
example : QProb.Equiv ((hypergeometricFromUrn 0 0 0 (by decide) (by decide)).pmf ⟨0, by decide⟩)
    QProb.one := by decide

/-- Generating functions recover law equality across distinct outcome types
and different denominator presentations. -/
example : (bernoulliNatDistro 1 1 (by decide)).SameLaw (binomialNatDistro 1 2 2 (by decide)) :=
  NatDistro.sameLaw_of_pgf_largeNat _ _ (by decide)
example : decodeCounts 3 3 (encodeCounts 3 [2, 0, 1]) = [2, 0, 1] := by decide

/-- Categorical sampling includes zero-weight categories and the empty word. -/
example : QProb.Equiv
    ((categoricalOccupancyDistro 3 [2, 0, 1] (by decide)).pmf [2, 0, 1])
    ⟨4, 9, by decide⟩ := by decide
example : QProb.Equiv
    ((categoricalOccupancyDistro 0 [0, 2] (by decide)).pmf [0, 0]) QProb.one := by decide

/-- Merging categories permits empty destination categories. Coordinate
marginals retain deterministic endpoints, and covariance is signed. -/
example : aggregateCounts 3 [0, 1, 0] [2, 0, 1] = [3, 0, 0] := by decide
example : QProb.Equiv
    (((multinomialDistro 3 [2, 0, 1] (by decide)).map (aggregateCounts 3 [0, 1, 0])).pmf [3, 0, 0])
    QProb.one := by decide
example : QProb.Equiv (variance (multinomialCoordinate 3 [2, 0, 1] (by decide) 0))
    ⟨2, 3, by decide⟩ := by decide
example : QProb.Equiv (mean (multinomialCoordinate 3 [2, 0, 1] (by decide) 1)) QProb.zero := by decide
example : SignedMoment.Equiv
    ((multinomialDistro 3 [2, 0, 1] (by decide)).covariance
      (fun counts => counts.getD 0 0) (fun counts => counts.getD 2 0))
    ⟨-2, 3, by decide⟩ := by decide
example : SignedMoment.Equiv
    ((multinomialDistro 0 [2, 1] (by decide)).covariance
      (fun counts => counts.getD 0 0) (fun counts => counts.getD 1 0))
    ⟨0, 1, by decide⟩ := by decide

/-- Multicolour reinforcement, its occupancy coefficient, zero colours and
empty sampling are checked on the actual finite records. -/
example : QProb.Equiv ((multicolourPolyaDistro 2 [1, 1, 0] (by decide)).pmf [0, 0])
    ⟨1, 3, by decide⟩ := by decide
example : QProb.Equiv ((multicolourPolyaDistro 3 [1, 2, 0] (by decide)).pmf [0, 1, 1])
    ⟨1, 10, by decide⟩ := by decide
example : QProb.Equiv ((multicolourPolyaDistro 3 [1, 2, 0] (by decide)).pmf [1, 0, 1])
    ⟨1, 10, by decide⟩ := by decide
example : QProb.Equiv ((dirichletMultinomialDistro 3 [1, 2, 0] (by decide)).pmf [1, 2, 0])
    ⟨3, 10, by decide⟩ := by decide
example : QProb.Equiv ((dirichletMultinomialDistro 3 [0, 2, 0] (by decide)).pmf [0, 3, 0])
    QProb.one := by decide
example : QProb.Equiv ((dirichletMultinomialDistro 3 [0, 2, 0] (by decide)).pmf [1, 2, 0])
    QProb.zero := by decide
example : QProb.Equiv ((dirichletMultinomialDistro 0 [1] (by decide)).pmf [0])
    QProb.one := by decide
example : QProb.Equiv ((dirichletMultinomialDistro 0 [1] (by decide)).pmf [])
    QProb.zero := by decide
example : (dirichletMultinomialCoordinate 3 [0, 2] (by decide) 0).SameLaw
    (betaBinomialNatDistroOfTotal 3 0 2 (by decide)) :=
  dirichletMultinomial_two_coordinate 3 0 2 (by decide)

/-- Rational kernel presentations may change all integer weights while
retaining the full Gaussian and squared-coordinate laws. -/
example : (discreteGaussianDistro 2 ⟨1, 2, by decide⟩ (by change 1 ≤ 2; decide)).SameLaw
    (discreteGaussianDistro 2 ⟨2, 4, by decide⟩ (by change 2 ≤ 4; decide)) :=
  discreteGaussian_sameLaw_kernel 2 _ _ (by change 1 ≤ 2; decide) (by change 2 ≤ 4; decide) (by decide)
example : (chiSquaredDistro 3 2 ⟨1, 2, by decide⟩ (by change 1 ≤ 2; decide)).SameLaw
    (chiSquaredDistro 3 2 ⟨2, 4, by decide⟩ (by change 2 ≤ 4; decide)) :=
  chiSquared_sameLaw_kernel 3 2 _ _ (by change 1 ≤ 2; decide) (by change 2 ≤ 4; decide) (by decide)
example : (discreteGaussianDistro 0 ⟨0, 7, by decide⟩ (by change 0 ≤ 7; decide)).SameLaw
    (discreteGaussianDistro 0 QProb.zero (QProb.zero_le _)) :=
  discreteGaussian_sameLaw_kernel 0 _ _ (by change 0 ≤ 7; decide) (QProb.zero_le _) (by decide)

end Thesis.Examples.DistributionExtensions
