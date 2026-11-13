import Thesis.Probability.FiniteGibbsGrouping

namespace Thesis.Probability.FiniteGibbsGrouping
open ConstructiveReal

/-- The bit-logarithm of the actual counted physical multiplicity. -/
def logDegeneracy (grouping : FiniteGibbsGrouping micro groups features) (j : Fin groups) : ConstructiveReal :=
  (ofSignedRatio (grouping.states.reference j).toSignedRatio).positiveLog2 (grouping.states.reference j) (le_refl _)

private theorem difference_cancel (first second : ConstructiveReal) : Equiv (add (sub first second) second) first :=
  equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _)
    (equiv_trans (add_comm _ _) (add_neg second))) (add_zero _))

/-- Entropy lost by grouping physical microstates is the macrostate-weighted
log degeneracy. This is proved for the actual aggregated Gibbs law using
partition and feature-mean preservation, not postulated as an entropy rule.
The formula in natural units retains the established bit calibration. -/
theorem entropy_natural_correction (grouping : FiniteGibbsGrouping micro groups features)
    (parameters : Fin features → ConstructiveReal) :
    Equiv (mul (grouping.microFamily.entropy parameters) lnTwo)
      (add (mul (grouping.macroFamily.entropy parameters) lnTwo)
        (grouping.macroFamily.expectation parameters grouping.macroFamily.logReference)) := by
  let common := add (grouping.macroFamily.logPartition parameters)
    (FiniteLinear.pair features parameters (fun k => grouping.macroFamily.expectation parameters (grouping.macroFamily.feature k)))
  let correction := grouping.macroFamily.expectation parameters grouping.macroFamily.logReference
  have referenceZero : Equiv (grouping.microFamily.expectation parameters grouping.microFamily.logReference) zero :=
    equiv_trans ((grouping.microFamily.asTilt parameters).expectation_congr one _ _
      (fun i => positiveLn_one PositiveRatio.one (le_refl one)))
      ((grouping.microFamily.asTilt parameters).expectation_constant one zero)
  have microFormula : Equiv (mul (grouping.microFamily.entropy parameters) lnTwo) common :=
    equiv_trans (grouping.microFamily.entropy_partition parameters) (equiv_trans
      (add_congr (add_congr (grouping.logPartition_eq parameters)
        (FiniteLinear.pair_congr features parameters parameters _ _ (fun _ => equiv_refl _) (grouping.feature_mean parameters)))
        (neg_congr referenceZero))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _)))
  have macroFormula : Equiv (add (mul (grouping.macroFamily.entropy parameters) lnTwo) correction) common :=
    equiv_trans (add_congr (grouping.macroFamily.entropy_partition parameters) (equiv_refl correction)) (difference_cancel common correction)
  exact equiv_trans microFormula (equiv_symm macroFormula)

theorem degeneracy_mean_units (grouping : FiniteGibbsGrouping micro groups features)
    (parameters : Fin features → ConstructiveReal) :
    Equiv (grouping.macroFamily.expectation parameters grouping.macroFamily.logReference)
      (mul (grouping.macroFamily.expectation parameters grouping.logDegeneracy) lnTwo) :=
  equiv_trans ((grouping.macroFamily.asTilt parameters).expectation_congr one _ _ (fun j => mul_comm _ _))
    (equiv_trans ((grouping.macroFamily.asTilt parameters).expectation_scale one lnTwo grouping.logDegeneracy) (mul_comm _ _))

/-- In bits, H_micro = H_macro + E_macro[log2(g)]. Each `g` was computed
from distinct physical indices. Repeated distribution-record atoms do not
enter the grouping data or this multiplicity. -/
theorem entropy_bits_correction (grouping : FiniteGibbsGrouping micro groups features)
    (parameters : Fin features → ConstructiveReal) :
    Equiv (grouping.microFamily.entropy parameters)
      (add (grouping.macroFamily.entropy parameters) (grouping.macroFamily.expectation parameters grouping.logDegeneracy)) := by
  have multiplied := equiv_trans (grouping.entropy_natural_correction parameters)
    (equiv_trans (add_congr (equiv_refl _) (grouping.degeneracy_mean_units parameters)) (equiv_symm (add_mul _ _ _)))
  have leftScaled := equiv_trans (mul_comm lnTwo (grouping.microFamily.entropy parameters))
    (equiv_trans multiplied (mul_comm _ lnTwo))
  exact ⟨(mul_le_mul_positive_iff lnTwo RationalLogSecant.limit.positiveInverseLower lnTwo_lower _ _).mp leftScaled.1,
    (mul_le_mul_positive_iff lnTwo RationalLogSecant.limit.positiveInverseLower lnTwo_lower _ _).mp leftScaled.2⟩

end Thesis.Probability.FiniteGibbsGrouping
