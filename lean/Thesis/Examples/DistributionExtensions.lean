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

/-- Signed coordinates, dependent cancellation and independent products
use the same finite probability records and retain exact negative values. -/
example : (SignedMoment.ofInt (-1)).Equiv
    ((bernoulliDistro 1 1 (by decide)).signedCovariance
      (fun bit : Bool => if bit then 1 else -1) (fun bit : Bool => if bit then -1 else 1)) := by decide
example : QProb.Equiv ((bernoulliDistro 1 1 (by decide)).varianceInt
    (fun bit : Bool => if bit then 1 else -1)) QProb.one := by decide
example : QProb.Equiv ((bernoulliDistro 1 1 (by decide)).varianceInt
    (fun bit : Bool => (if bit then 1 else -1) + (if bit then -1 else 1))) QProb.zero := by decide
example : ((bernoulliDistro 1 1 (by decide)).covariance
    (fun bit : Bool => if bit then 1 else 0) (fun bit : Bool => if bit then 0 else 1)).Equiv
    ⟨-1, 4, by decide⟩ := by decide
example : (((bernoulliDistro 1 2 (by decide)).product (bernoulliDistro 3 1 (by decide))).signedCovariance
    (fun pair => if pair.1 then 2 else -3) (fun pair => if pair.2 then -4 else 1)).Equiv
    (SignedMoment.ofInt 0) :=
  Distro.signedCovariance_independent _ _ (fun bit : Bool => if bit then 2 else -3) (fun bit : Bool => if bit then -4 else 1)

/-- The reinforcement increment changes the actual path and occupancy law. -/
example : QProb.Equiv ((reinforcedUrnDistro 3 [1, 2] 2 (by decide)).pmf [0, 0, 1])
    ⟨2, 35, by decide⟩ := by decide
example : QProb.Equiv ((reinforcedCountDistro 3 [1, 2] 2 (by decide)).pmf [2, 1])
    ⟨6, 35, by decide⟩ := by decide
example : (reinforcedCountDistro 3 [1, 2] 0 (by decide)).SameLaw
    (multinomialDistro 3 [1, 2] (by decide)) := reinforcedCount_zero 3 [1, 2] (by decide)
example : QProb.Equiv ((reinforcedCountDistro 3 [0, 2, 0] 4 (by decide)).pmf [0, 3, 0])
    QProb.one := by decide
/-- Clearing rational parameters also scales reinforcement, retaining unit
reinforcement in parameter units rather than rounding the initial ratios. -/
example : QProb.Equiv
    ((rationalPolyaDistro 2 [⟨1, 2, by decide⟩, ⟨3, 2, by decide⟩] (by decide)).pmf [0, 0])
    ⟨1, 8, by decide⟩ := by decide
example : QProb.Equiv
    ((rationalDirichletMultinomialDistro 2 [⟨1, 2, by decide⟩, ⟨3, 2, by decide⟩] (by decide)).pmf [1, 1])
    ⟨1, 4, by decide⟩ := by decide
example : (rationalPolyaDistro 2 [⟨1, 2, by decide⟩, ⟨3, 2, by decide⟩] (by decide)).SameLaw
    (rationalPolyaDistro 2 [⟨2, 4, by decide⟩, ⟨6, 4, by decide⟩] (by decide)) := by
  apply rationalPolya_sameLaw_parameters
  constructor
  · rfl
  · intro index
    cases index with
    | zero => decide
    | succ index => cases index with
        | zero => decide
        | succ index => simp only [List.getD_cons_succ, List.getD_nil]; exact QProb.equiv_refl _

/-- Joint orders involve several coordinates and need not lie below the
trial count. All family formulas include zero-weight coordinates. -/
example : QProb.Equiv (jointFactorialMoment (multinomialDistro 5 [2, 1, 3] (by decide)) [2, 1, 0])
    ⟨10, 9, by decide⟩ := by decide
example : QProb.Equiv (jointFactorialMoment (dirichletMultinomialDistro 5 [2, 1, 3] (by decide)) [2, 1, 0])
    ⟨15, 14, by decide⟩ := by decide
example : QProb.Equiv (jointFactorialMoment (reinforcedCountDistro 5 [2, 1, 3] 2 (by decide)) [2, 1, 0])
    QProb.one := by decide
example : QProb.Equiv (jointFactorialMoment (dirichletMultinomialDistro 5 [2, 1, 3] (by decide)) [2, 2, 2])
    QProb.zero := by decide
example : QProb.Equiv (jointFactorialMoment (dirichletMultinomialDistro 5 [0, 2, 1] (by decide)) [1, 1, 0])
    QProb.zero := by decide
example : QProb.Equiv (jointFactorialMoment
    (rationalDirichletMultinomialDistro 3 [⟨1, 2, by decide⟩, ⟨3, 2, by decide⟩] (by decide)) [1, 1])
    ⟨3, 4, by decide⟩ := by decide

/-- Coarsening retains reinforcement, empty groups and deterministic colours. -/
example : QProb.Equiv
    (((dirichletMultinomialDistro 3 [1, 2, 3] (by decide)).map (aggregateCounts 3 [0, 1, 0])).pmf [2, 1, 0])
    ⟨5, 14, by decide⟩ := by decide
example : (dirichletMultinomialCoordinate 4 [2, 0, 3] (by decide) 2).SameLaw
    (betaBinomialNatDistroOfTotal 4 3 2 (by decide)) :=
  dirichletMultinomial_coordinate_betaBinomial 4 [2, 0, 3] (by decide) 2 (by decide)
example : QProb.Equiv (mean (dirichletMultinomialCoordinate 4 [2, 0, 3] (by decide) 2))
    ⟨12, 5, by decide⟩ := by decide
example : QProb.Equiv (variance (dirichletMultinomialCoordinate 4 [2, 0, 3] (by decide) 2))
    ⟨36, 25, by decide⟩ := by decide
example : (dirichletMultinomialCoordinate 4 [0, 2, 0] (by decide) 1).SameLaw
    (betaBinomialNatDistroOfTotal 4 2 0 (by decide)) :=
  dirichletMultinomial_coordinate_betaBinomial 4 [0, 2, 0] (by decide) 1 (by decide)

/-- Reinforcement increases the magnitude of off-diagonal count covariance. -/
example : ((reinforcedCountDistro 4 [2, 0, 3] 2 (by decide)).covariance
    (fun counts => counts.getD 0 0) (fun counts => counts.getD 2 0)).Equiv
    ⟨-312, 175, by decide⟩ := by decide
example : ((dirichletMultinomialDistro 4 [2, 0, 3] (by decide)).covariance
    (fun counts => counts.getD 0 0) (fun counts => counts.getD 2 0)).Equiv
    ⟨-36, 25, by decide⟩ := by decide
example : ((dirichletMultinomialDistro 4 [2, 0, 3] (by decide)).covariance
    (fun counts => counts.getD 0 0) (fun counts => counts.getD 1 0)).Equiv
    (SignedMoment.ofInt 0) := by decide

/-- Conditioning on counts sums over all possible observed orders. -/
example : (reinforcedCountsContinuation 2 2 [1, 2, 1] [1, 0, 1] 2 (by decide) (by decide)
    (by decide)).SameLaw (reinforcedUrnDistro 2 [3, 2, 3] 2 (by decide)) :=
  reinforcedCountsContinuation_updated 2 2 [1, 2, 1] [1, 0, 1] 2 (by decide) (by decide) (by decide)
example : QProb.Equiv ((reinforcedCountsContinuation 2 2 [1, 2, 1] [1, 0, 1] 2 (by decide) (by decide)
    (by decide)).pmf [0, 0]) ⟨3, 16, by decide⟩ := by decide
example : QProb.Equiv ((reinforcedCountsContinuation 2 1 [1, 2, 1] [1, 0, 1] 2 (by decide) (by decide)
    (by decide)).pmf [1]) ⟨1, 4, by decide⟩ := by decide
example : QProb.Equiv ((reinforcedUrnDistro 3 [1, 2, 1] 2 (by decide)).pmf [0, 1, 2])
    ((reinforcedUrnDistro 3 [1, 2, 1] 2 (by decide)).pmf [2, 0, 1]) := by decide
example : QProb.Equiv ((reinforcedCountsContinuation 2 1 [0, 2, 0] [0, 2, 0] 3 (by decide) (by decide)
    (by decide)).pmf [1]) QProb.one := by decide

example : (reinforcedPrefixContinuation [0, 2] 2 [1, 2, 1] 2 (by decide) (by decide)).SameLaw
    (reinforcedCountsContinuation 2 2 [1, 2, 1] [1, 0, 1] 2 (by decide) (by decide) (by decide)) :=
  reinforcedPrefix_counts_sufficient [0, 2] 2 [1, 2, 1] 2 (by decide) (by decide)
example : QProb.Equiv ((reinforcedPrefixContinuation [0, 2] 1 [1, 2, 1] 2 (by decide) (by decide)).pmf [0])
    ⟨3, 8, by decide⟩ := by decide

end Thesis.Examples.DistributionExtensions

namespace Thesis.Probability.Distros

/-- A zero-weight colour is retained while the reinforced variance can
exceed the binomial variance. These computations check the actual records. -/
example : QProb.Equiv (variance (reinforcedCountCoordinate 3 [2, 0, 1] 2 (by decide) 0))
    (⟨6, 5, by decide⟩ : QProb) := by decide +kernel

example : QProb.Equiv (variance (reinforcedCountCoordinate 3 [2, 0, 1] 0 (by decide) 0))
    (⟨2, 3, by decide⟩ : QProb) := by decide +kernel

example : QProb.Equiv (variance (reinforcedCountCoordinate 0 [2, 0, 1] 2 (by decide) 0))
    QProb.zero := by decide +kernel

example : QProb.Equiv (variance (reinforcedCountCoordinate 3 [2, 0, 1] 2 (by decide) 1))
    QProb.zero := by decide +kernel

end Thesis.Probability.Distros

namespace Thesis.Probability.Distros

/-- Fractional parameters use unit reinforcement in rational units. -/
example : QProb.Equiv
    ((rationalBetaBinomialNatDistro 2 ⟨1, 2, by decide⟩ ⟨3, 2, by decide⟩ (by decide)).distro.record.probVal
      (fun counts => decide (counts.getD 0 0 = 2)))
    (⟨1, 8, by decide⟩ : QProb) := by decide +kernel

example : QProb.Equiv
    ((rationalCountsContinuation 2 1 [⟨1, 2, by decide⟩, QProb.zero, ⟨3, 2, by decide⟩] [1, 0, 1]
      (by decide) (by decide +kernel)).pmf [0])
    (⟨3, 8, by decide⟩ : QProb) := by decide +kernel

end Thesis.Probability.Distros

namespace Thesis.Probability.Distros

/-- The signed extension handles a negative value without changing the
nonnegative probability record. -/
example : QProb.Equiv ((bernoulliDistro 1 1 (by decide)).varianceInt
    (fun bit => if bit then (1 : Int) else -1)) QProb.one := by decide +kernel

example : QProb.Equiv ((bernoulliDistro 0 1 (by decide)).varianceInt
    (fun bit => if bit then (7 : Int) else -3)) QProb.zero := by decide +kernel

example : QProb.LE
    (SignedMoment.square ((bernoulliDistro 1 1 (by decide)).signedCovariance
      (fun bit => if bit then (1 : Int) else -1)
      (fun bit => if bit then (-1 : Int) else 1))) QProb.one := by
  unfold QProb.LE
  decide +kernel

end Thesis.Probability.Distros

namespace Thesis.Probability.Distros

example : SignedRatio.Equiv ((bernoulliDistro 1 1 (by decide)).rationalVariance
    (fun bit => (⟨if bit then 1 else -1, 2, by decide⟩ : SignedRatio)))
    (⟨1, 4, by decide⟩ : SignedRatio) := by decide +kernel

end Thesis.Probability.Distros

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- A zero-weight outlier and an empty event cell do not change the
nonintegral conditional means of the four equally likely values. -/
def partitionMomentFixture : Distro Nat :=
  ⟨⟨[(0, 1), (1, 1), (2, 1), (3, 1), (99, 0)], 4, by decide, rfl⟩⟩

def partitionMomentCells : AtomPartition partitionMomentFixture :=
  AtomPartition.ofEvents partitionMomentFixture [fun x => decide (x < 2), fun _ => false]

def partitionMomentObservable (x : Nat) : SignedRatio := ⟨x, 1, by decide⟩

example : SignedRatio.Equiv
    (partitionMomentCells.distro.rationalExpectation (fun cell => conditionalBlockVariance cell partitionMomentObservable))
    (⟨1, 4, by decide⟩ : SignedRatio) := by decide +kernel

example : SignedRatio.Equiv
    (partitionMomentCells.distro.rationalVariance (fun cell => conditionalBlockMean cell partitionMomentObservable))
    SignedRatio.one := by decide +kernel

example : SignedRatio.Equiv (partitionMomentFixture.rationalVariance partitionMomentObservable)
    (⟨5, 4, by decide⟩ : SignedRatio) := by decide +kernel

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

example : QProb.Equiv (jointFactorialMoment (multivariateHypergeometricDistro 2 [2, 0, 1] (by decide)) [1, 0, 1])
    (⟨2, 3, by decide⟩ : QProb) := by decide +kernel

example : QProb.Equiv (jointFactorialMoment (multivariateHypergeometricDistro 2 [2, 0, 1] (by decide)) [4, 0, 0])
    QProb.zero := by decide +kernel

example : QProb.Equiv (((multivariateHypergeometricDistro 2 [2, 0, 1] (by decide)).map
    (aggregateCounts 3 [1, 0, 1])).pmf [0, 2, 0]) QProb.one := by decide +kernel

example : QProb.Equiv ((multivariateHypergeometricDistro 0 [] (by decide)).pmf []) QProb.one := by decide +kernel

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Rational observables keep exact boundary events, signed covariance,
and equivalence of unreduced constant values. -/
def halfSignedBit (bit : Bool) : SignedRatio := ⟨if bit then 1 else -1, 2, by decide⟩

example : QProb.Equiv ((bernoulliDistro 1 1 (by decide)).varianceRational halfSignedBit)
    ⟨1, 4, by decide⟩ := by decide +kernel

example : QProb.Equiv ((bernoulliDistro 1 1 (by decide)).record.probVal
    ((bernoulliDistro 1 1 (by decide)).rationalDeviationEvent halfSignedBit ⟨1, 2, by decide⟩))
    QProb.one := by decide +kernel

example : QProb.LE ((bernoulliDistro 1 1 (by decide)).record.probVal
    ((bernoulliDistro 1 1 (by decide)).rationalDeviationEvent halfSignedBit ⟨1, 2, by decide⟩))
    (QProb.div ((bernoulliDistro 1 1 (by decide)).varianceRational halfSignedBit)
      (QProb.mul ⟨1, 2, by decide⟩ ⟨1, 2, by decide⟩) (by decide)) :=
  Distro.chebyshev_rationalObservable _ halfSignedBit ⟨1, 2, by decide⟩ (by decide)

example : SignedRatio.Equiv ((bernoulliDistro 1 1 (by decide)).rationalCovariance
    halfSignedBit (fun bit => SignedRatio.neg (halfSignedBit bit))) ⟨-1, 4, by decide⟩ := by decide +kernel

example : ∃ c : SignedRatio, (bernoulliDistro 1 1 (by decide)).AlmostSurely
    (fun bit => SignedRatio.Equiv (if bit then (⟨1, 2, by decide⟩ : SignedRatio) else ⟨2, 4, by decide⟩) c) :=
  (Distro.rationalVariance_zero_iff_constant _ _).mp (by decide +kernel)

example : ∃ c : SignedRatio, (bernoulliDistro 0 1 (by decide)).AlmostSurely
    (fun bit => SignedRatio.Equiv (if bit then (⟨17, 3, by decide⟩ : SignedRatio) else ⟨-3, 2, by decide⟩) c) :=
  (Distro.rationalVariance_zero_iff_constant _ _).mp (by decide +kernel)

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

def residueFour (x : Nat) : Fin 4 := ⟨x % 4, Nat.mod_lt _ (by decide)⟩
def mergePairs (value : Fin 4) : Fin 2 := ⟨value.val / 2, by omega⟩
def threeEvidenceCells (x : Nat) : Fin 3 := if x < 2 then 0 else if x < 4 then 1 else 2

/-- Refinement uses actual rational conditional means, with a nontrivial
coarse cell and the retained zero-weight outlier. -/
example : SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation (fun x => mergePairs (residueFour x))
      (partitionMomentFixture.conditionalExpectation residueFour partitionMomentObservable) 2)
    ⟨5, 2, by decide⟩ := by decide +kernel

example (x : Nat) : SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation (fun y => mergePairs (residueFour y))
      (partitionMomentFixture.conditionalExpectation residueFour partitionMomentObservable) x)
    (partitionMomentFixture.conditionalExpectation (fun y => mergePairs (residueFour y)) partitionMomentObservable x) :=
  Distro.conditionalExpectation_tower _ residueFour mergePairs partitionMomentObservable x

example : SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable 99)
    SignedRatio.zero := by decide +kernel

example : SignedRatio.Equiv
    (partitionMomentFixture.rationalExpectation (fun x => SignedRatio.mul
      (⟨(threeEvidenceCells x).val, 2, by decide⟩ : SignedRatio)
      (SignedRatio.sub (partitionMomentObservable x)
        (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable x))))
    SignedRatio.zero := by decide +kernel

example : SignedRatio.Equiv
    (partitionMomentFixture.rationalExpectation (fun x => SignedRatio.mul
      (⟨(threeEvidenceCells x).val, 2, by decide⟩ : SignedRatio)
      (SignedRatio.sub (partitionMomentObservable x)
        (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable x))))
    SignedRatio.zero := Distro.conditionalExpectation_orthogonal partitionMomentFixture threeEvidenceCells partitionMomentObservable
      (fun label => (⟨label.val, 2, by decide⟩ : SignedRatio))

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Ordered removal distinguishes word probabilities from occupancy probabilities. -/
example : QProb.Equiv ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [0, 2])
    ⟨1, 3, by decide⟩ := by decide +kernel

example : QProb.Equiv (((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).map (colourCounts 3)).pmf [1, 0, 1])
    ⟨2, 3, by decide⟩ := by decide +kernel

example : QProb.Equiv ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [1, 0])
    QProb.zero := by decide +kernel

example : ¬ depletingCountsSupported 1 [2, 0, 1] [0, 1, 0] := by decide +kernel

example : QProb.Equiv ((multicolourDepletingDistro 0 [] (by decide)).pmf []) QProb.one := by decide +kernel

example : depletingState [2, 0, 1] [1, 0, 1] = [1, 0, 0] := by decide

example : QProb.Equiv ((depletingCountsContinuation 1 1 [2, 0, 1] [1, 0, 0] (by decide) (by decide +kernel)).pmf [2])
    ⟨1, 2, by decide⟩ := by decide +kernel

example : QProb.Equiv ((depletingPrefixContinuation [0, 0] 1 [2, 0, 1] (by decide) (by decide +kernel)).pmf [2])
    QProb.one := by decide +kernel

example : (depletingPrefixContinuation [0] 2 [2, 0, 1] (by decide) (by decide +kernel)).SameLaw
    (depletingCountsContinuation 1 2 [2, 0, 1] [1, 0, 0] (by decide) (by decide +kernel)) :=
  depletingPrefix_counts_sufficient [0] 2 [2, 0, 1] (by decide) (by decide +kernel)

example : QProb.Equiv ((depletingCountsContinuation 3 0 [2, 0, 1] [2, 0, 1] (by decide) (by decide +kernel)).pmf [])
    QProb.one := by decide +kernel

example : QProb.Equiv ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).record.probVal (fun word =>
    depletingCountsEvent 1 3 [1, 0, 0] word && decide (colourCounts 3 (word.drop 1) = [0, 0, 1])))
    ⟨1, 3, by decide⟩ := by decide +kernel

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Correlation is retained while duplicate and zero-weight presentations
are allowed to differ. Every count vector has dimension two and bound one. -/
def jointMomentFixture : Distro (List Nat) :=
  ofWeightedAtoms [([0, 0], 1), ([1, 1], 1), ([0, 1], 0)] (by decide)

def jointMomentDuplicateFixture : Distro (List Nat) :=
  ofWeightedAtoms [([1, 1], 2), ([0, 0], 1), ([0, 0], 1)] (by decide)

def jointMomentAntiFixture : Distro (List Nat) :=
  ofWeightedAtoms [([0, 1], 1), ([1, 0], 1)] (by decide)

example : QProb.Equiv (jointFactorialMoment jointMomentFixture [1, 1]) ⟨1, 2, by decide⟩ := by decide +kernel
example : QProb.Equiv (jointFactorialMoment jointMomentAntiFixture [1, 1]) QProb.zero := by decide +kernel
example : QProb.Equiv (jointMomentFixture.expectNat (fun counts => counts.getD 0 0))
    (jointMomentAntiFixture.expectNat (fun counts => counts.getD 0 0)) := by decide +kernel
example : QProb.Equiv (jointMomentFixture.expectNat (fun counts => counts.getD 1 0))
    (jointMomentAntiFixture.expectNat (fun counts => counts.getD 1 0)) := by decide +kernel

/-- A nonintegral offset and a value greater than one test the full
nonnegative-rational expansion; the mixed coefficient contributes. -/
example : QProb.Equiv (multivariatePGF jointMomentFixture
    ([⟨1, 2, by decide⟩, QProb.ofNat 2].map (fun t => QProb.add t QProb.one)))
    ⟨11, 4, by decide⟩ := by decide +kernel

example : QProb.Equiv (QProb.listSum ((factorialBox 2 1).map (fun orders =>
    QProb.mul (multivariateFactorialCoefficient jointMomentFixture orders)
      (multivariateMonomial [⟨1, 2, by decide⟩, QProb.ofNat 2] orders))))
    ⟨11, 4, by decide⟩ := by decide +kernel

example (args : List QProb) (dimension : args.length = 2) :
    QProb.Equiv (multivariatePGF jointMomentFixture (args.map (fun t => QProb.add t QProb.one)))
      (QProb.listSum ((factorialBox args.length 1).map (fun orders =>
        QProb.mul (multivariateFactorialCoefficient jointMomentFixture orders) (multivariateMonomial args orders)))) := by
  apply multivariatePGF_factorial_expansion
  intro atom member
  change atom ∈ [([0, 0], 1), ([1, 1], 1), ([0, 1], 0)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact ⟨dimension.symm, by decide +kernel⟩

/-- Matching the complete finite rectangle reconstructs every joint event,
even with reordered atoms, duplicates, a zero weight, and changed denominator. -/
example : jointMomentFixture.SameLaw jointMomentDuplicateFixture := by
  apply Distro.sameLaw_of_jointFactorialMoments _ _ 2 1
  · intro atom member
    change atom ∈ [([0, 0], 1), ([1, 1], 1), ([0, 1], 0)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals decide +kernel
  · intro atom member
    change atom ∈ [([1, 1], 2), ([0, 0], 1), ([0, 0], 1)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals decide +kernel
  · intro orders dimension bounded
    cases orders with
    | nil => simp only [List.length_nil] at dimension; omega
    | cons first rest => cases rest with
        | nil => simp only [List.length_cons, List.length_nil] at dimension; omega
        | cons second rest =>
            have empty : rest = [] := List.length_eq_zero_iff.mp (by
              simp only [List.length_cons] at dimension
              omega)
            subst rest
            have firstBound := bounded first (List.mem_cons_self ..)
            have secondBound := bounded second (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            have firstCases : first = 0 ∨ first = 1 := by omega
            have secondCases : second = 0 ∨ second = 1 := by omega
            rcases firstCases with rfl | rfl <;> rcases secondCases with rfl | rfl <;> decide +kernel

/-- Zero dimensions and a zero bound retain the single empty monomial. -/
example : QProb.Equiv (multivariatePGF (Distro.pointMass ([] : List Nat)) [])
    (QProb.listSum ((factorialBox 0 0).map (fun orders =>
      QProb.mul (multivariateFactorialCoefficient (Distro.pointMass ([] : List Nat)) orders)
        (multivariateMonomial [] orders)))) := by decide +kernel

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Negative values, unreduced fractions and an irrelevant zero-weight
outlier exercise the signed rational algebra on an actual finite record. -/
def rationalAlgebraFixture : Distro Nat := ofWeightedAtoms [(0, 1), (1, 1), (99, 0)] (by decide)
def rationalAlgebraFirst (x : Nat) : SignedRatio :=
  if x = 0 then ⟨-3, 2, by decide⟩ else if x = 1 then ⟨2, 4, by decide⟩ else ⟨17, 3, by decide⟩
def rationalAlgebraSecond (x : Nat) : SignedRatio :=
  if x = 0 then ⟨4, 6, by decide⟩ else if x = 1 then ⟨-1, 3, by decide⟩ else ⟨-47, 5, by decide⟩

example : SignedRatio.Equiv (rationalAlgebraFixture.rationalCovariance rationalAlgebraFirst rationalAlgebraSecond)
    ⟨-1, 2, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (rationalAlgebraFixture.rationalCovariance
    (fun x => SignedRatio.mul ⟨-4, 6, by decide⟩ (rationalAlgebraFirst x)) rationalAlgebraSecond)
    ⟨1, 3, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (rationalAlgebraFixture.rationalVariance
    (fun x => SignedRatio.add (rationalAlgebraFirst x) (rationalAlgebraSecond x)))
    ⟨1, 4, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (rationalAlgebraFixture.rationalVariance
    (fun x => SignedRatio.mul ⟨-4, 6, by decide⟩ (rationalAlgebraFirst x)))
    ⟨4, 9, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv ((rationalAlgebraFixture.product rationalAlgebraFixture).rationalExpectation
    (fun pair => SignedRatio.mul (rationalAlgebraFirst pair.1) (rationalAlgebraSecond pair.2)))
    ⟨-1, 12, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv ((rationalAlgebraFixture.product rationalAlgebraFixture).rationalCovariance
    (fun pair => rationalAlgebraFirst pair.1) (fun pair => rationalAlgebraSecond pair.2)) SignedRatio.zero :=
  Distro.rationalCovariance_independent _ _ rationalAlgebraFirst rationalAlgebraSecond

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Correct supported fibre means coexist with an arbitrary value on the
retained null fibre. Uniqueness is consequently almost sure. -/
def conditionalPrediction (label : Fin 3) : SignedRatio :=
  if label.val = 0 then ⟨1, 2, by decide⟩ else if label.val = 1 then ⟨5, 2, by decide⟩ else ⟨-97, 3, by decide⟩

example : partitionMomentFixture.AlmostSurely (fun x => SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable x)
    (conditionalPrediction (threeEvidenceCells x))) :=
  Distro.conditionalExpectation_unique _ threeEvidenceCells partitionMomentObservable conditionalPrediction (by decide +kernel)

example : ¬ SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable 99)
    (conditionalPrediction (threeEvidenceCells 99)) := by decide +kernel

example : SignedRatio.Equiv (partitionMomentFixture.conditionalExpectation threeEvidenceCells
    (fun x => SignedRatio.mul (conditionalPrediction (threeEvidenceCells x)) (partitionMomentObservable x)) 99)
    SignedRatio.zero := by decide +kernel

example : SignedRatio.Equiv (partitionMomentFixture.rationalSquaredError partitionMomentObservable
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable))
    ⟨1, 4, by decide⟩ := by decide +kernel

example : SignedRatio.Equiv (partitionMomentFixture.rationalExpectation (fun x => SignedRatio.mul
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable x)
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable x)))
    ⟨13, 4, by decide⟩ := by decide +kernel

example : SignedRatio.LE (partitionMomentFixture.rationalSquaredError partitionMomentObservable
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable))
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable (fun _ => SignedRatio.zero)) :=
  Distro.conditionalExpectation_least_squares _ threeEvidenceCells partitionMomentObservable (fun _ => SignedRatio.zero)

example : SignedRatio.LE (partitionMomentFixture.rationalExpectation (fun x => SignedRatio.mul
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable x)
    (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable x)))
    (partitionMomentFixture.rationalExpectation (fun x => SignedRatio.mul (partitionMomentObservable x) (partitionMomentObservable x))) :=
  Distro.conditionalExpectation_square_contraction _ threeEvidenceCells partitionMomentObservable

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- The fixed total and dimension hold almost surely despite a retained
zero-weight empty vector with a different dimension and total. -/
def highestMomentFixture : Distro (List Nat) := ofWeightedAtoms [([0, 2], 1), ([1, 1], 1), ([], 0)] (by decide)

example : QProb.Equiv (highestMomentFixture.pmf [0, 2])
    (QProb.div (jointFactorialMoment highestMomentFixture [0, 2])
      (QProb.ofNat (orderFactorial [0, 2])) (orderFactorial_pos _)) :=
  Distro.pmf_of_highestFactorialMoment _ 2 _ (by decide +kernel) (by decide)

example : highestMomentFixture.SameLaw (highestMomentFixture.rescaleWeights 3 (by decide)) :=
  Distro.sameLaw_of_highestFactorialMoments _ _ 2 2 (by decide +kernel) (by decide +kernel)
    (fun orders _ _ => (highestMomentFixture.rescaleWeights_sameLaw 3 (by decide)).symm.jointFactorialMoment orders)

example : QProb.Equiv ((multinomialDistro 3 [1, 0, 2] (by decide)).pmf [1, 0, 2]) ⟨4, 9, by decide⟩ :=
  QProb.equiv_trans (multinomial_pmf_highestOrder 3 [1, 0, 2] [1, 0, 2] (by decide) (by decide) (by decide))
    (by decide +kernel)

example : QProb.Equiv ((multinomialDistro 3 [1, 0, 2] (by decide)).pmf [1, 1, 1]) QProb.zero :=
  QProb.equiv_trans (multinomial_pmf_highestOrder 3 [1, 0, 2] [1, 1, 1] (by decide) (by decide) (by decide))
    (by decide +kernel)

example : QProb.Equiv ((reinforcedCountDistro 3 [1, 0, 2] 2 (by decide)).pmf [1, 0, 2]) ⟨8, 35, by decide⟩ :=
  QProb.equiv_trans (reinforcedCount_pmf_highestOrder 3 2 [1, 0, 2] [1, 0, 2] (by decide) (by decide) (by decide))
    (by decide +kernel)

example : QProb.Equiv ((multivariateHypergeometricDistro 3 [2, 0, 3] (by decide)).pmf [1, 0, 2]) ⟨3, 5, by decide⟩ :=
  QProb.equiv_trans (multivariateHypergeometric_pmf_highestOrder 3 [2, 0, 3] [1, 0, 2] (by decide) (by decide) (by decide))
    (by decide +kernel)

example : QProb.Equiv ((multivariateHypergeometricDistro 0 [] (by decide)).pmf []) QProb.one :=
  QProb.equiv_trans (multivariateHypergeometric_pmf_highestOrder 0 [] [] (by decide) (by decide) (by decide))
    (by decide +kernel)

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Feasible counts suffice, including an exhausted population and zero stocks. -/
example : depletingCountsSupported 3 [2, 0, 1] [2, 0, 1] :=
  (depletingCountsSupported_iff_coordinates _ _ _).mpr (by decide +kernel)

example : depletingCountsSupported 0 [] [] :=
  (depletingCountsSupported_iff_coordinates _ _ _).mpr (by decide +kernel)

example : ¬ depletingCountsSupported 1 [2, 0, 1] [0, 1, 0] := by
  intro supported
  have data := (depletingCountsSupported_iff_coordinates _ _ _).mp supported
  have impossible := data.2.2 1 (by decide)
  change 1 ≤ 0 at impossible
  omega

example : ¬ depletingCountsSupported 0 [0, 0] [] := by
  intro supported
  have data := (depletingCountsSupported_iff _ _ _).mp supported
  have impossible : (0 : Nat) = 2 := data.1
  omega

example : QProb.Equiv ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [0, 2])
    ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [2, 0]) :=
  multicolourDepleting_exchangeable [2, 0, 1] [0, 2] [2, 0] (by decide) (List.Perm.swap ..)

/-- Both an exhausted colour and an invalid colour retain the exchangeability law. -/
example : QProb.Equiv ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [1, 0])
    ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [0, 1]) :=
  multicolourDepleting_exchangeable [2, 0, 1] [1, 0] [0, 1] (by decide) (List.Perm.swap ..)

example : QProb.Equiv ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [7, 0])
    ((multicolourDepletingDistro 2 [2, 0, 1] (by decide)).pmf [0, 7]) :=
  multicolourDepleting_exchangeable [2, 0, 1] [7, 0] [0, 7] (by decide) (List.Perm.swap ..)

example : QProb.Equiv ((depletingCountsContinuationOfBounds 1 1 [1, 1, 1] [1, 0, 0]
    (by decide) (by decide) (by decide) (by decide +kernel)).pmf [1]) ⟨1, 2, by decide⟩ :=
  depleting_next_after_counts_of_bounds _ _ _ (by decide) (by decide) (by decide) (by decide +kernel) _ (by decide)

example : QProb.Equiv ((depletingCountsContinuationOfBounds 3 0 [2, 0, 1] [2, 0, 1]
    (by decide) (by decide) (by decide) (by decide +kernel)).pmf []) QProb.one := by decide +kernel

end Thesis.Examples.DistributionExtensions

namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Three retained null outliers violate dimension, coordinate bounds, or both. -/
def positiveOutlierFixture : Distro (List Nat) :=
  ofWeightedAtoms [([0, 0], 1), ([1, 1], 1), ([], 0), ([200, 0], 0), ([300, 400, 500], 0)] (by decide)

theorem positiveOutlier_shape : positiveOutlierFixture.AlmostSurely
    (fun counts => counts.length = 2 ∧ ∀ count ∈ counts, count ≤ 1) := by decide +kernel

example : positiveOutlierFixture.record.atoms =
    [([0, 0], 1), ([1, 1], 1), ([], 0), ([200, 0], 0), ([300, 400, 500], 0)] := rfl

example : ¬ ∀ atom ∈ positiveOutlierFixture.record.atoms, atom.1.length = 2 := by decide +kernel
example : ¬ ∀ atom ∈ positiveOutlierFixture.record.atoms, ∀ count ∈ atom.1, count ≤ 1 := by decide +kernel

/-- Null outliers do not affect any order, including orders outside the rectangle. -/
theorem positiveOutlier_moments (orders : List Nat) :
    QProb.Equiv (jointFactorialMoment positiveOutlierFixture orders) (jointFactorialMoment jointMomentFixture orders) := by
  simp only [jointFactorialMoment, Distro.expectNat, positiveOutlierFixture, jointMomentFixture,
    ofWeightedAtoms, natIntegral, FiniteProbRecord.totalMass, QProb.Equiv,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero]

/-- The new bounded interface applies with bound one despite recorded values 500. -/
theorem positiveOutlier_sameLaw : positiveOutlierFixture.SameLaw jointMomentFixture :=
  Distro.sameLaw_of_jointFactorialMoments_positiveSupport _ _ 2 1 positiveOutlier_shape
    (by decide +kernel) (fun orders _ _ => positiveOutlier_moments orders)

example : positiveOutlierFixture.SameLaw jointMomentFixture :=
  (Distro.sameLaw_iff_jointFactorialMoments_positiveSupport _ _ 2
    (fun atom member weight => (positiveOutlier_shape atom member weight).1) (by decide +kernel)).mpr
      (fun orders _ => positiveOutlier_moments orders)

example (args : List QProb) (dimension : args.length = 2) :
    QProb.Equiv (multivariatePGF positiveOutlierFixture (args.map (fun t => QProb.add t QProb.one)))
      (QProb.listSum ((factorialBox args.length 1).map (fun orders =>
        QProb.mul (multivariateFactorialCoefficient positiveOutlierFixture orders) (multivariateMonomial args orders)))) :=
  multivariatePGF_factorial_expansion_positiveSupport _ args 1 (fun atom member weight =>
    ⟨(positiveOutlier_shape atom member weight).1.trans dimension.symm, (positiveOutlier_shape atom member weight).2⟩)

/-- Positional PGF uniqueness also accepts the same wrong-shaped null atoms. -/
example : positiveOutlierFixture.SameLaw jointMomentFixture :=
  Distro.sameLaw_of_multivariatePGF_positiveSupport _ _ 2 2 (by decide)
    (fun atom member weight => ⟨(positiveOutlier_shape atom member weight).1,
      fun count within => Nat.lt_succ_of_le ((positiveOutlier_shape atom member weight).2 count within)⟩)
    (by decide +kernel) (fun args _ => positiveOutlier_sameLaw.expectation (multivariateMonomial args))

def emptyPositiveOutlierFixture : Distro (List Nat) := ofWeightedAtoms [([], 2), ([9, 10], 0)] (by decide)

example : emptyPositiveOutlierFixture.SameLaw (Distro.pointMass ([] : List Nat)) := by
  apply Distro.sameLaw_of_jointFactorialMoments_positiveSupport _ _ 0 0 (by decide +kernel) (by decide +kernel)
  intro orders dimension _
  have empty : orders = [] := List.length_eq_zero_iff.mp dimension
  subst orders
  decide +kernel

/-- Numeric expansion and reconstruction also ignore a retained out-of-bound null value. -/
def positiveNumericOutlierFixture : NatDistro Nat := ⟨rationalAlgebraFixture, id⟩
def positiveNumericCleanFixture : NatDistro Nat := ⟨ofWeightedAtoms [(0, 1), (1, 1)] (by decide), id⟩

example (t : QProb) : QProb.Equiv (pgf positiveNumericOutlierFixture (QProb.add t QProb.one))
    (QProb.listSum ((List.range 2).map (fun order =>
      QProb.mul (factorialPGFCoefficient positiveNumericOutlierFixture order) (qpow t order)))) :=
  pgf_factorial_expansion_positiveSupport _ 1 (by decide +kernel) t

example : positiveNumericOutlierFixture.SameLaw positiveNumericCleanFixture := by
  apply NatDistro.sameLaw_of_factorialMoments_positiveSupport _ _ 1 (by decide +kernel) (by decide +kernel)
  intro order bound
  have alternatives : order = 0 ∨ order = 1 := by omega
  rcases alternatives with rfl | rfl <;> decide +kernel

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Highest-order extraction includes zero trials with retained zero-weight colours. -/
example : QProb.Equiv ((multinomialDistro 0 [0, 1] (by decide)).pmf [0, 0]) QProb.one :=
  QProb.equiv_trans (multinomial_pmf_highestOrder 0 [0, 1] [0, 0] (by decide) (by decide) (by decide))
    (by decide +kernel)

example : QProb.Equiv ((reinforcedCountDistro 0 [0, 1] 2 (by decide)).pmf [0, 0]) QProb.one :=
  QProb.equiv_trans (reinforcedCount_pmf_highestOrder 0 2 [0, 1] [0, 0] (by decide) (by decide) (by decide))
    (by decide +kernel)

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Equivalent unreduced responses may differ arbitrarily at a retained null atom. -/
def equivalentPredictionResponse (x : Nat) : SignedRatio :=
  if x = 0 then ⟨-6, 4, by decide⟩ else if x = 1 then ⟨1, 2, by decide⟩ else ⟨-100, 1, by decide⟩

example : SignedRatio.Equiv (rationalAlgebraFixture.rationalSquaredError rationalAlgebraFirst equivalentPredictionResponse)
    SignedRatio.zero :=
  (Distro.rationalSquaredError_zero_iff _ _ _).mpr (by decide +kernel)

example : rationalAlgebraFixture.AlmostSurely (fun x => SignedRatio.Equiv
    (rationalAlgebraFirst x) (equivalentPredictionResponse x)) :=
  (Distro.rationalSquaredError_zero_iff _ _ _).mp (by decide +kernel)

example : ¬ SignedRatio.Equiv (rationalAlgebraFixture.rationalSquaredError rationalAlgebraFirst (fun _ => SignedRatio.zero))
    SignedRatio.zero := by decide +kernel

/-- An optimal predictor can take a different value on an unsupported label. -/
example : SignedRatio.Equiv (partitionMomentFixture.rationalSquaredError partitionMomentObservable
    (fun x => conditionalPrediction (threeEvidenceCells x)))
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable
      (partitionMomentFixture.conditionalExpectation threeEvidenceCells partitionMomentObservable)) :=
  (Distro.conditionalExpectation_optimal_iff _ _ _ _).mpr (by decide +kernel)

example : SignedRatio.LE (rationalAlgebraFixture.rationalSquaredError
    (rationalAlgebraFixture.conditionalExpectation threeEvidenceCells rationalAlgebraFirst)
    (rationalAlgebraFixture.conditionalExpectation threeEvidenceCells rationalAlgebraSecond))
    (rationalAlgebraFixture.rationalSquaredError rationalAlgebraFirst rationalAlgebraSecond) :=
  Distro.conditionalExpectation_squaredError_contraction _ _ _ _

example : SignedRatio.Equiv (rationalAlgebraFixture.rationalSquaredError
    (rationalAlgebraFixture.conditionalExpectation threeEvidenceCells rationalAlgebraFirst)
    (rationalAlgebraFixture.conditionalExpectation threeEvidenceCells rationalAlgebraSecond)) ⟨4, 9, by decide⟩ := by decide +kernel

/-- Fine and coarse labels deliberately fail to refine at the null outcome 99. -/
def predictionFine (x : Nat) : Fin 4 := ⟨x % 4, Nat.mod_lt _ (by decide)⟩
def predictionCoarse (x : Nat) : Fin 2 := if x = 99 then 0 else if x < 2 then 0 else 1
def predictionMerge (label : Fin 4) : Fin 2 := if label.val < 2 then 0 else 1

example : predictionCoarse 99 ≠ predictionMerge (predictionFine 99) := by decide +kernel

example : SignedRatio.LE (partitionMomentFixture.rationalSquaredError partitionMomentObservable
    (partitionMomentFixture.conditionalExpectation predictionFine partitionMomentObservable))
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable
      (partitionMomentFixture.conditionalExpectation predictionCoarse partitionMomentObservable)) :=
  Distro.conditionalExpectation_error_refinement_almostSurely _ predictionFine predictionCoarse predictionMerge
    (by decide +kernel) partitionMomentObservable

example : SignedRatio.Equiv (partitionMomentFixture.rationalSquaredError partitionMomentObservable
    (partitionMomentFixture.conditionalExpectation predictionFine partitionMomentObservable)) SignedRatio.zero := by decide +kernel

example : SignedRatio.Equiv (partitionMomentFixture.rationalSquaredError partitionMomentObservable
    (partitionMomentFixture.conditionalExpectation predictionCoarse partitionMomentObservable)) ⟨1, 4, by decide⟩ := by decide +kernel

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

def varyingTotalNumeric : NatDistro Nat :=
  ⟨ofWeightedAtoms [(0, 1), (1, 2), (2, 1), (99, 0)] (by decide), id⟩

example (value : Nat) : SignedRatio.Equiv
    (varyingTotalNumeric.distro.record.probVal (fun x => decide (x = value))).toSignedRatio
    (inverseFactorialPMF varyingTotalNumeric 2 value) :=
  NatDistro.pmf_factorial_inversion _ 2 value (by decide +kernel)

/-- Actual cancellation is required: the zero-cell mass is 1 - 1 + 1/4. -/
example : SignedRatio.Equiv (inverseFactorialPMF varyingTotalNumeric 2 0) ⟨1, 4, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (inverseFactorialPMF varyingTotalNumeric 2 1) ⟨1, 2, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (inverseFactorialPMF varyingTotalNumeric 2 2) ⟨1, 4, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (inverseFactorialPMF varyingTotalNumeric 2 3) SignedRatio.zero := by decide +kernel

example : SignedRatio.Equiv
    ((Distro.pointMass (0 : Nat)).record.probVal (fun x => decide (x = 0))).toSignedRatio
    (inverseFactorialPMF (⟨Distro.pointMass (0 : Nat), id⟩ : NatDistro Nat) 0 0) :=
  NatDistro.pmf_factorial_inversion (⟨Distro.pointMass (0 : Nat), id⟩ : NatDistro Nat) 0 0 (by decide +kernel)

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

def varyingTotalJoint : Distro (List Nat) :=
  ofWeightedAtoms [([0, 0], 1), ([1, 0], 1), ([0, 2], 2), ([], 0), ([99, 88, 77], 0)] (by decide)

example : SignedRatio.Equiv (varyingTotalJoint.pmf [0, 0]).toSignedRatio
    (inverseJointFactorialPMF varyingTotalJoint 2 [0, 0]) :=
  Distro.pmf_jointFactorial_inversion _ _ _ (by decide +kernel)

example : SignedRatio.Equiv (inverseJointFactorialPMF varyingTotalJoint 2 [0, 0]) ⟨1, 4, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (inverseJointFactorialPMF varyingTotalJoint 2 [1, 0]) ⟨1, 4, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (inverseJointFactorialPMF varyingTotalJoint 2 [0, 2]) ⟨1, 2, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (inverseJointFactorialPMF varyingTotalJoint 2 [1, 1]) SignedRatio.zero := by decide +kernel
example : SignedRatio.Equiv (inverseJointFactorialPMF varyingTotalJoint 2 [3, 0]) SignedRatio.zero := by decide +kernel

example : SignedRatio.Equiv (emptyPositiveOutlierFixture.pmf []).toSignedRatio
    (inverseJointFactorialPMF emptyPositiveOutlierFixture 0 []) :=
  Distro.pmf_jointFactorial_inversion _ _ _ (by decide +kernel)

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

def occupancyTestCoefficients (i : Nat) : SignedRatio :=
  if i = 0 then ⟨-1, 2, by decide⟩ else if i = 1 then ⟨2, 3, by decide⟩ else SignedRatio.one

example : SignedRatio.Equiv (rationalAlgebraFixture.rationalVariance
    (rationalLinearCombination [0, 1, 0] occupancyTestCoefficients
      (fun i => if i = 0 then rationalAlgebraFirst else rationalAlgebraSecond)))
    (rationalAlgebraFixture.rationalCovarianceForm [0, 1, 0]
      (fun i => if i = 0 then rationalAlgebraFirst else rationalAlgebraSecond) occupancyTestCoefficients) :=
  Distro.rationalVariance_linearCombination _ _ _ _

example : SignedRatio.Nonnegative ((multinomialDistro 2 [1, 0, 2] (by decide)).occupancyCovarianceForm 3 occupancyTestCoefficients) :=
  multinomial_covarianceForm_nonnegative _ _ _ _
example : SignedRatio.Nonnegative ((reinforcedCountDistro 2 [1, 0, 2] 2 (by decide)).occupancyCovarianceForm 3 occupancyTestCoefficients) :=
  reinforcedCount_covarianceForm_nonnegative _ _ _ _ _
example : SignedRatio.Nonnegative ((multivariateHypergeometricDistro 2 [1, 0, 2] (by decide)).occupancyCovarianceForm 3 occupancyTestCoefficients) :=
  multivariateHypergeometric_covarianceForm_nonnegative _ _ _ _

example : SignedRatio.Equiv ((multinomialDistro 2 [1, 0, 2] (by decide)).occupancyCovarianceForm 3 (fun _ => SignedRatio.one)) SignedRatio.zero :=
  multinomial_covarianceForm_ones_zero _ _ _
example : SignedRatio.Equiv ((reinforcedCountDistro 2 [1, 0, 2] 2 (by decide)).occupancyCovarianceForm 3 (fun _ => SignedRatio.one)) SignedRatio.zero :=
  reinforcedCount_covarianceForm_ones_zero _ _ _ _
example : SignedRatio.Equiv ((multivariateHypergeometricDistro 2 [1, 0, 2] (by decide)).occupancyCovarianceForm 3 (fun _ => SignedRatio.one)) SignedRatio.zero :=
  multivariateHypergeometric_covarianceForm_ones_zero _ _ _

example : SignedRatio.Equiv ((multinomialDistro 2 [1, 0, 2] (by decide)).rationalCovariance (countResponse 1) (countResponse 0)) SignedRatio.zero :=
  multinomial_covariance_zero_weight _ _ _ _ _ (by decide) (by decide)
example : SignedRatio.Equiv ((reinforcedCountDistro 2 [1, 0, 2] 2 (by decide)).rationalCovariance (countResponse 1) (countResponse 0)) SignedRatio.zero :=
  reinforcedCount_covariance_zero_weight _ _ _ _ _ _ (by decide) (by decide)
example : SignedRatio.Equiv ((multivariateHypergeometricDistro 2 [1, 0, 2] (by decide)).rationalCovariance (countResponse 1) (countResponse 0)) SignedRatio.zero :=
  multivariateHypergeometric_covariance_zero_stock _ _ _ _ _ (by decide) (by decide)

/-- No total-minus-one denominator is required for empty or one-ball populations. -/
example : SignedRatio.Equiv ((multivariateHypergeometricDistro 0 [0, 0] (by decide)).rationalCovariance (countResponse 0) (countResponse 1)) SignedRatio.zero :=
  multivariateHypergeometric_covariance_zero_stock _ _ _ _ _ (by decide) (by decide)
example : SignedRatio.Equiv ((multivariateHypergeometricDistro 1 [1] (by decide)).occupancyCovarianceForm 1 occupancyTestCoefficients) SignedRatio.zero := by decide +kernel
example : SignedRatio.Equiv ((multinomialDistro 0 [1, 0, 2] (by decide)).occupancyCovarianceForm 3 occupancyTestCoefficients) SignedRatio.zero := by decide +kernel
example : SignedRatio.Equiv ((multivariateHypergeometricDistro 3 [1, 0, 2] (by decide)).occupancyCovarianceForm 3 occupancyTestCoefficients) SignedRatio.zero := by decide +kernel

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- A zero-stock source and two zero-stock destination groups remain explicit. -/
example : ((multicolourDepletingDistro 2 [1, 0, 2, 1] (by decide)).map
    (List.map (fun colour => ([0, 1, 0, 2] : List Nat).getD colour 0))).SameLaw
    (multicolourDepletingDistro 2 [3, 0, 1, 0] (by decide)) :=
  multicolourDepleting_aggregation 2 4 [1, 0, 2, 1] [0, 1, 0, 2] (by decide) (by decide) (by decide +kernel)

example : aggregateCounts 4 [0, 1, 0, 2] (depletingState [1, 0, 2, 1] [0, 0, 1, 0]) =
    depletingState [3, 0, 1, 0] [1, 0, 0, 0] :=
  aggregateCounts_depletingState_supported 1 4 [1, 0, 2, 1] [0, 1, 0, 2] [0, 0, 1, 0]
    (by decide) (by decide +kernel)

/-- Different fine observations with the same grouped counts give the same
complete future law after merging, not just the same next-draw mean. -/
example : ((depletingCountsContinuation 1 1 [1, 0, 2, 1] [0, 0, 1, 0] (by decide) (by decide +kernel)).map
    (List.map (fun colour => ([0, 1, 0, 2] : List Nat).getD colour 0))).SameLaw
    (depletingCountsContinuation 1 1 [3, 0, 1, 0] [1, 0, 0, 0] (by decide) (by decide +kernel)) :=
  depletingCountsContinuation_aggregation 1 1 4 [1, 0, 2, 1] [0, 1, 0, 2] [0, 0, 1, 0]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

example : ((depletingCountsContinuation 1 1 [1, 0, 2, 1] [1, 0, 0, 0] (by decide) (by decide +kernel)).map
    (List.map (fun colour => ([0, 1, 0, 2] : List Nat).getD colour 0))).SameLaw
    (depletingCountsContinuation 1 1 [3, 0, 1, 0] [1, 0, 0, 0] (by decide) (by decide +kernel)) :=
  depletingCountsContinuation_aggregation 1 1 4 [1, 0, 2, 1] [0, 1, 0, 2] [1, 0, 0, 0]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

example : ((multicolourDepletingDistro 0 [] (by decide)).map
    (List.map (fun colour => ([] : List Nat).getD colour 0))).SameLaw
    (multicolourDepletingDistro 0 [] (by decide)) :=
  multicolourDepleting_aggregation 0 0 [] [] (by decide) (by decide) (by decide +kernel)

example : ((multicolourDepletingDistro 0 [] (by decide)).map
    (List.map (fun colour => ([] : List Nat).getD colour 0))).SameLaw
    (multicolourDepletingDistro 0 [0, 0, 0] (by decide)) :=
  multicolourDepleting_aggregation 0 3 [] [] (by decide) (by decide) (by decide +kernel)

example : ((depletingCountsContinuation 2 0 [1, 0, 1] [1, 0, 1] (by decide) (by decide +kernel)).map
    (List.map (fun colour => ([0, 1, 0] : List Nat).getD colour 0))).SameLaw
    (depletingCountsContinuation 2 0 [2, 0, 0] [2, 0, 0] (by decide) (by decide +kernel)) :=
  depletingCountsContinuation_aggregation 2 0 3 [1, 0, 1] [0, 1, 0] [1, 0, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

/-- Raw event masses also merge when the horizon is impossible. -/
example (event : Event (List Nat)) :
    FiniteProbRecord.eventMass (multicolourDepletingAtoms 3 [1, 0, 1])
      (fun word => event (word.map (fun colour => ([0, 1, 0] : List Nat).getD colour 0))) =
    FiniteProbRecord.eventMass (multicolourDepletingAtoms 3 [2, 0, 0]) event :=
  multicolourDepleting_eventMass_aggregation 3 3 [1, 0, 1] [0, 1, 0] (by decide) (by decide +kernel) event

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- The label refinement is deliberately false at the retained null outcome. -/
example : SignedRatio.Equiv
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable
      (partitionMomentFixture.conditionalExpectation predictionCoarse partitionMomentObservable))
    (SignedRatio.add
      (partitionMomentFixture.rationalSquaredError partitionMomentObservable
        (partitionMomentFixture.conditionalExpectation predictionFine partitionMomentObservable))
      (partitionMomentFixture.rationalSquaredError
        (partitionMomentFixture.conditionalExpectation predictionFine partitionMomentObservable)
        (partitionMomentFixture.conditionalExpectation predictionCoarse partitionMomentObservable))) :=
  Distro.conditionalExpectation_refinement_gain_almostSurely _ predictionFine predictionCoarse predictionMerge
    (by decide +kernel) partitionMomentObservable

example : SignedRatio.Equiv (partitionMomentFixture.rationalSquaredError
    (partitionMomentFixture.conditionalExpectation predictionFine partitionMomentObservable)
    (partitionMomentFixture.conditionalExpectation predictionCoarse partitionMomentObservable)) ⟨1, 4, by decide⟩ := by decide +kernel

example : ¬ SignedRatio.Equiv
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable
      (partitionMomentFixture.conditionalExpectation predictionCoarse partitionMomentObservable))
    (partitionMomentFixture.rationalSquaredError partitionMomentObservable
      (partitionMomentFixture.conditionalExpectation predictionFine partitionMomentObservable)) := by decide +kernel

/-- Refinement gives no improvement for a constant response. -/
example : SignedRatio.Equiv
    (partitionMomentFixture.rationalSquaredError (fun _ => SignedRatio.one)
      (partitionMomentFixture.conditionalExpectation predictionCoarse (fun _ => SignedRatio.one)))
    (partitionMomentFixture.rationalSquaredError (fun _ => SignedRatio.one)
      (partitionMomentFixture.conditionalExpectation predictionFine (fun _ => SignedRatio.one))) :=
  (Distro.conditionalExpectation_refinement_equal_iff_almostSurely _ predictionFine predictionCoarse predictionMerge
    (by decide +kernel) (fun _ => SignedRatio.one)).mpr (by decide +kernel)

example : partitionMomentFixture.AlmostSurely (fun x => SignedRatio.Equiv
    (partitionMomentFixture.conditionalExpectation predictionFine (fun _ => SignedRatio.one) x)
    (partitionMomentFixture.conditionalExpectation predictionCoarse (fun _ => SignedRatio.one) x)) :=
  (Distro.conditionalExpectation_refinement_equal_iff_almostSurely _ predictionFine predictionCoarse predictionMerge
    (by decide +kernel) (fun _ => SignedRatio.one)).mp (by decide +kernel)

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

example : SignedRatio.Equiv ((multivariateHypergeometricDistro 2 [1, 0, 2] (by decide)).rationalCovariance
    (countResponse 0) (countResponse 2)) ⟨-2, 9, by decide⟩ :=
  SignedRatio.equiv_trans
    (multivariateHypergeometric_rationalCovariance 2 [1, 0, 2] (by decide) (by decide) 0 2 (by decide) (by decide) (by decide))
    (by decide +kernel)

example : SignedRatio.Equiv ((multivariateHypergeometricDistro 0 [1, 0, 2] (by decide)).rationalCovariance
    (countResponse 0) (countResponse 2)) SignedRatio.zero :=
  SignedRatio.equiv_trans
    (multivariateHypergeometric_rationalCovariance 0 [1, 0, 2] (by decide) (by decide) 0 2 (by decide) (by decide) (by decide))
    (by decide +kernel)

example : SignedRatio.Equiv ((multivariateHypergeometricDistro 3 [1, 0, 2] (by decide)).rationalCovariance
    (countResponse 0) (countResponse 2)) SignedRatio.zero :=
  SignedRatio.equiv_trans
    (multivariateHypergeometric_rationalCovariance 3 [1, 0, 2] (by decide) (by decide) 0 2 (by decide) (by decide) (by decide))
    (by decide +kernel)

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- Tight unequal bounds, varying totals, a zero-width axis, and retained
null outliers of both the wrong shape and excessive coordinates. -/
def rectangleMomentFixture : Distro (List Nat) :=
  ofWeightedAtoms [([0, 0, 0], 1), ([1, 0, 2], 2), ([0, 0, 1], 1), ([], 0), ([99, 99, 99, 99], 0)] (by decide)

example : (factorialRectangle [1, 0, 2]).length = 6 := by decide +kernel
example : factorialRectangle [0, 0] = [[0, 0]] := by decide +kernel
example : factorialRectangle [] = [[]] := rfl

example (args : List QProb) (dimension : args.length = 3) :
    QProb.Equiv (multivariatePGF rectangleMomentFixture (args.map (fun t => QProb.add t QProb.one)))
      (QProb.listSum ((factorialRectangle [1, 0, 2]).map (fun orders =>
        QProb.mul (multivariateFactorialCoefficient rectangleMomentFixture orders) (multivariateMonomial args orders)))) :=
  multivariatePGF_factorial_expansion_rectangle rectangleMomentFixture args [1, 0, 2]
    (by simpa only [List.length_cons, List.length_nil] using dimension.symm) (by decide +kernel)

example : SignedRatio.Equiv (rectangleMomentFixture.pmf [1, 0, 2]).toSignedRatio
    (inverseRectangleFactorialPMF rectangleMomentFixture [1, 0, 2] [1, 0, 2]) :=
  Distro.pmf_rectangleFactorial_inversion _ _ _ (by decide) (by decide +kernel)

example : SignedRatio.Equiv (inverseRectangleFactorialPMF rectangleMomentFixture [1, 0, 2] [1, 0, 2])
    ⟨1, 2, by decide⟩ := by decide +kernel
example : SignedRatio.Equiv (inverseRectangleFactorialPMF rectangleMomentFixture [1, 0, 2] [1, 0, 1])
    SignedRatio.zero := by decide +kernel
example : SignedRatio.Equiv (inverseRectangleFactorialPMF rectangleMomentFixture [1, 0, 2] [2, 0, 0])
    SignedRatio.zero := by decide +kernel

example : SignedRatio.Equiv (emptyPositiveOutlierFixture.pmf []).toSignedRatio
    (inverseRectangleFactorialPMF emptyPositiveOutlierFixture [] []) :=
  Distro.pmf_rectangleFactorial_inversion _ _ _ rfl (by decide +kernel)

def rectangleMomentOther : Distro (List Nat) :=
  ofWeightedAtoms [([0, 0, 1], 2), ([0, 0, 0], 2), ([1, 0, 2], 4), ([0, 7], 0)] (by decide)

private theorem rectangle_fixture_moments (orders : List Nat) (within : CoordinateBounds orders [1, 0, 2]) :
    QProb.Equiv (jointFactorialMoment rectangleMomentFixture orders) (jointFactorialMoment rectangleMomentOther orders) := by
  cases orders with
  | nil => exact False.elim within
  | cons a orders => cases orders with
      | nil => exact False.elim within.2
      | cons b orders => cases orders with
          | nil => exact False.elim within.2.2
          | cons c orders => cases orders with
              | cons d orders => exact False.elim within.2.2.2
              | nil =>
                  have first : a = 0 ∨ a = 1 := by have bound := within.1; omega
                  have middle : b = 0 := by have bound := within.2.1; omega
                  have last : c = 0 ∨ c = 1 ∨ c = 2 := by have bound := within.2.2.1; omega
                  subst b
                  rcases first with rfl | rfl <;> rcases last with rfl | rfl | rfl <;> decide +kernel

/-- Six actual rectangle moments suffice despite different raw null records. -/
example : rectangleMomentFixture.SameLaw rectangleMomentOther :=
  Distro.sameLaw_of_rectangleFactorialMoments _ _ [1, 0, 2]
    (by decide +kernel) (by decide +kernel) rectangle_fixture_moments

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

def gridExampleProbability (value : Nat) : QProb :=
  if value = 0 then ⟨1, 3, by decide⟩ else if value = 2 then ⟨2, 3, by decide⟩ else QProb.zero

example : QProb.Equiv ((probabilityGrid 2 gridExampleProbability (by decide +kernel)).pmf 2) ⟨2, 3, by decide⟩ :=
  probabilityGrid_pmf _ _ _ _ (by decide)
example : (1, 0) ∈ (probabilityGrid 2 gridExampleProbability (by decide +kernel)).record.atoms := by decide +kernel
example : ∃ weight, (1, weight) ∈ (probabilityGrid 2 gridExampleProbability (by decide +kernel)).record.atoms :=
  probabilityGrid_retains _ _ _ _ (by decide)

end Thesis.Examples.DistributionExtensions


namespace Thesis.Examples.DistributionExtensions
open Probability Probability.Distros

/-- E[(X)₀]=E[(X)₁]=E[(X)₂]=1 corresponds to equal mass at zero and two. -/
def suppliedFactorialTable (order : Nat) : QProb := if order ≤ 2 then QProb.one else QProb.zero

theorem suppliedFactorialTable_valid : FactorialMomentTableValid suppliedFactorialTable 2 := by
  constructor
  · intro value within
    have alternatives : value = 0 ∨ value = 1 ∨ value = 2 := by omega
    rcases alternatives with rfl | rfl | rfl <;> decide +kernel
  · decide +kernel

example (order : Nat) (within : order ≤ 2) :
    QProb.Equiv (factorialMoment (realizedFactorialDistro suppliedFactorialTable 2 suppliedFactorialTable_valid) order)
      (suppliedFactorialTable order) := realizedFactorialDistro_moments _ _ _ _ within

example : SignedRatio.Equiv
    ((realizedFactorialDistro suppliedFactorialTable 2 suppliedFactorialTable_valid).distro.pmf 0).toSignedRatio
    ⟨1, 2, by decide⟩ :=
  SignedRatio.equiv_trans (realizedFactorialDistro_pmf _ _ _ 0 (by decide)) (by decide +kernel)

example : (1, 0) ∈ (realizedFactorialDistro suppliedFactorialTable 2 suppliedFactorialTable_valid).distro.record.atoms := by decide +kernel

/-- Uniqueness compares laws across different weighted and null presentations. -/
def suppliedTableOther : Distro Nat := ofWeightedAtoms [(0, 1), (2, 1), (99, 0)] (by decide)

example : suppliedTableOther.SameLaw (realizedFactorialDistro suppliedFactorialTable 2 suppliedFactorialTable_valid).distro := by
  apply realizedFactorialDistro_unique _ _ _ _ (by decide +kernel)
  intro order within
  have alternatives : order = 0 ∨ order = 1 ∨ order = 2 := by omega
  rcases alternatives with rfl | rfl | rfl <;> decide +kernel

/-- A normalized inverse can still be invalid through a negative cell. -/
def negativeCellFactorialTable (order : Nat) : QProb :=
  if order = 0 then QProb.one else if order = 2 then QProb.ofNat 2 else QProb.zero

theorem negativeCellFactorialTable_invalid : ¬ FactorialMomentTableValid negativeCellFactorialTable 2 := by
  intro valid
  have negative : ¬ SignedRatio.Nonnegative (inverseFactorialTable negativeCellFactorialTable 2 1) := by decide +kernel
  exact negative (valid.1 1 (by decide))

example : ¬ ∃ μ : Distro Nat, μ.AlmostSurely (fun value => value ≤ 2) ∧
    ∀ order, order ≤ 2 → QProb.Equiv (factorialMoment (⟨μ, id⟩ : NatDistro Nat) order) (negativeCellFactorialTable order) := by
  intro realized
  exact negativeCellFactorialTable_invalid ((factorialMomentTable_realizable_iff negativeCellFactorialTable 2).mpr realized)

example : ¬ FactorialMomentTableValid (fun _ => QProb.zero) 0 := by
  intro valid
  have impossible : ¬ SignedRatio.Equiv (SignedRatio.listSum ((List.range 1).map (inverseFactorialTable (fun _ => QProb.zero) 0)))
      SignedRatio.one := by decide +kernel
  exact impossible valid.2

example : FactorialMomentTableValid (fun _ => QProb.one) 0 := by
  constructor
  · intro value within
    have zero : value = 0 := by omega
    subst value
    decide +kernel
  · decide +kernel

end Thesis.Examples.DistributionExtensions
