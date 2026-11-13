import Thesis.Probability.ConstructiveRealGibbsFamily
import Thesis.Probability.ConstructiveRealLogInverse

namespace Thesis.Probability.FiniteGibbsFamily
open ConstructiveReal
open Distros.RationalLinear

/-- The feature observable in the original rational coefficient units. -/
def feature (family : FiniteGibbsFamily states features) (j : Fin features) (i : Fin states) : ConstructiveReal :=
  ofSignedRatio (family.response j i)

def unitDirection (j : Fin features) (k : Fin features) : ConstructiveReal := realInteger (if k = j then 1 else 0)

theorem score_unit (family : FiniteGibbsFamily states features) (j : Fin features) (i : Fin states) :
    Equiv (family.score (unitDirection j) i) (family.feature j i) :=
  equiv_trans (realRationalDot_pair features (fun k => family.response k i) (unitDirection j))
    (equiv_trans (FiniteLinear.pair_comm features _ _) (FiniteLinear.pair_unit features j _))

theorem covariance_observables_congr (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal)
    (first first' second second' : Fin states → ConstructiveReal)
    (sameFirst : ∀ i, Equiv (first i) (first' i)) (sameSecond : ∀ i, Equiv (second i) (second' i)) :
    Equiv (family.covariance parameters first second) (family.covariance parameters first' second') :=
  add_congr ((family.asTilt parameters).expectation_congr one _ _ (fun i => mul_congr (sameFirst i) (sameSecond i)))
    (neg_congr (mul_congr ((family.asTilt parameters).expectation_congr one _ _ sameFirst)
      ((family.asTilt parameters).expectation_congr one _ _ sameSecond)))

/-- Exact directional log-partition derivative at the original parameter
vector. The returned certificate includes an explicit effective modulus. -/
def logPartition_directional (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal) :
    HasDerivativeAt (fun t => family.logPartition (shift parameters direction t)) zero
      (neg (family.expectation parameters (family.score direction))) :=
  (((family.along parameters direction).logPartition_hasDerivativeAt zero).function_congr
    (fun t => FiniteGibbsTilt.logPartition_congr (fun i => equiv_symm (family.along_logWeight parameters direction t i)))).slope_congr
      (neg_congr (FiniteGibbsTilt.expectation_compare (family.along_zero parameters direction) _))

/-- Variation of any fixed observable is minus covariance with the response
in the chosen parameter direction. Observables and directions may be signed. -/
def expectation_directional (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal)
    (observable : Fin states → ConstructiveReal) :
    HasDerivativeAt (fun t => family.expectation (shift parameters direction t) observable) zero
      (neg (family.covariance parameters observable (family.score direction))) :=
  (((family.along parameters direction).expectation_hasDerivativeAt zero observable).function_congr
    (fun t => FiniteGibbsTilt.expectation_compare (fun i => equiv_symm (family.along_logWeight parameters direction t i)) observable)).slope_congr
      (neg_congr (FiniteGibbsTilt.covariance_compare (family.along_zero parameters direction) _ _))

/-- Each natural-log partition partial derivative is the negative mean of
its original feature. This statement concerns the actual affine parameter
path, not an assumed formal differentiation operator. -/
def logPartition_partial (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) (j : Fin features) :
    HasDerivativeAt (fun t => family.logPartition (shift parameters (unitDirection j) t)) zero
      (neg (family.expectation parameters (family.feature j))) :=
  (family.logPartition_directional parameters (unitDirection j)).slope_congr
    (neg_congr ((family.asTilt parameters).expectation_congr one _ _ (family.score_unit j)))

/-- Mixed natural-log partition partials form the covariance matrix.
Redundant features may yield singular curvature; no positive-definite or
independent-feature hypothesis is silently imposed. -/
def logPartition_mixed (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) (j k : Fin features) :
    HasDerivativeAt (fun t => neg (family.expectation (shift parameters (unitDirection k) t) (family.feature j))) zero
      (family.covariance parameters (family.feature j) (family.feature k)) :=
  ((family.expectation_directional parameters (unitDirection k) (family.feature j)).neg).slope_congr
    (equiv_trans (neg_neg _) (family.covariance_observables_congr parameters _ _ _ _ (fun _ => equiv_refl _) (family.score_unit k)))

/-- In every parameter direction, log-partition curvature is a variance. -/
def logPartition_secondDirectional (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal) :
    HasDerivativeAt (fun t => neg (family.expectation (shift parameters direction t) (family.score direction))) zero
      (family.covariance parameters (family.score direction) (family.score direction)) :=
  ((family.expectation_directional parameters direction (family.score direction)).neg).slope_congr (neg_neg _)

theorem directional_curvature_nonnegative (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal) :
    LE zero (family.covariance parameters (family.score direction) (family.score direction)) :=
  (family.asTilt parameters).variance_nonnegative one _

/-- Weighted feature means and multipliers give the expected score by finite
bilinear Fubini, including repeated feature positions. -/
theorem expectation_score (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) :
    Equiv (family.expectation parameters (family.score parameters))
      (FiniteLinear.pair features parameters (fun j => family.expectation parameters (family.feature j))) :=
  equiv_trans (FiniteLinear.pair_congr states _ _ (fun i => family.mass parameters i) (fun i => family.mass parameters i)
    (fun i => equiv_trans (realRationalDot_pair features (fun j => family.response j i) parameters) (FiniteLinear.pair_comm features _ _))
    (fun _ => equiv_refl _))
    (FiniteLinear.combination_pair features states (fun j i => family.feature j i) parameters (family.mass parameters))

/-- Multivariate entropy dual identity with the reference-weight correction.
For unit reference weights, the final term vanishes. -/
theorem entropy_partition (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) :
    Equiv (mul (family.entropy parameters) lnTwo)
      (sub (add (family.logPartition parameters)
        (FiniteLinear.pair features parameters (fun j => family.expectation parameters (family.feature j))))
        (family.expectation parameters family.logReference)) :=
  equiv_trans ((family.asTilt parameters).entropy_partition one)
    (add_congr (add_congr (equiv_refl _) (equiv_trans (one_mul _) (family.expectation_score parameters))) (equiv_refl _))

def log2Partition (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) : ConstructiveReal :=
  (family.asTilt parameters).log2Partition one

/-- Bit log-partition gradients differ by the independently proved factor
`1/ln(2)`, including along arbitrary multivariate directions. -/
def log2Partition_directional (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal) :
    HasDerivativeAt (fun t => family.log2Partition (shift parameters direction t)) zero
      (neg (mul (family.expectation parameters (family.score direction)) RationalLogSecant.limit)) :=
  (((family.logPartition_directional parameters direction).mul_constant RationalLogSecant.limit).function_congr
    (fun t => equiv_symm (positiveLog2_from_positiveLn _ _ _))).slope_congr (neg_mul _ _)

theorem score_zero (family : FiniteGibbsFamily states features) (i : Fin states) :
    Equiv (family.score (fun _ => zero) i) zero :=
  equiv_trans (realRationalDot_pair features (fun j => family.response j i) _) (FiniteLinear.pair_zero_second features _)

/-- At zero parameters, unnormalized weights are exactly the supplied
rational reference weights. Normalization may then give an exact rational
candidate; general nonzero parameters have no such rationality guarantee. -/
theorem weight_zero (family : FiniteGibbsFamily states features) (i : Fin states) :
    Equiv ((family.asTilt (fun _ => zero)).weight one i) (ofSignedRatio (family.reference i).toSignedRatio) := by
  have logarithm : Equiv ((family.asTilt (fun _ => zero)).logWeight one i) (family.logReference i) :=
    equiv_trans (add_congr (equiv_trans (one_mul _) (neg_congr (family.score_zero i))) (equiv_refl _))
      (equiv_trans (add_congr (equiv_symm (ofSignedRatio_neg SignedRatio.zero)) (equiv_refl _)) (zero_add _))
  exact equiv_trans (exp_congr logarithm) (exp_positiveLn _ (family.reference i) (le_refl _))

end Thesis.Probability.FiniteGibbsFamily
