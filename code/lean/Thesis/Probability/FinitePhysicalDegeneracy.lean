import Thesis.Probability.FiniteGibbsGroupingCompatibility
import Thesis.Probability.FiniteStatisticalEntropy

/-!
# Statistical entropy under finite physical grouping

Reference: E. T. Jaynes, Information Theory and Statistical Mechanics,
Physical Review 106 (1957), 620, doi:10.1103/PhysRev.106.620.
Distinct physical states and their observables are modeling inputs. The
results below count those states and prove exact aggregation; they do not
establish empirical adequacy or identify thermodynamic entropy by definition.
-/

namespace Thesis.Probability.FiniteGibbsGrouping
open ConstructiveReal
open FiniteStatisticalMechanics

/-- S_micro = S_macro + kB*E_macro[ln(g)], for the actual degeneracy-weighted
macrostate law. Statistical entropy uses the proved ln(2) bit conversion. -/
theorem physical_entropy_correction (grouping : FiniteGibbsGrouping micro groups features)
    (parameters : Fin features → ConstructiveReal) (boltzmann : PositiveRatio) :
    Equiv (statisticalEntropy boltzmann (grouping.microFamily.entropy parameters))
      (add (statisticalEntropy boltzmann (grouping.macroFamily.entropy parameters))
        (mul (ofSignedRatio boltzmann.toSignedRatio) (grouping.macroFamily.expectation parameters grouping.macroFamily.logReference))) :=
  equiv_trans (mul_congr (equiv_refl _) (mul_comm _ _))
    (equiv_trans (mul_congr (equiv_refl _) (grouping.entropy_natural_correction parameters))
      (equiv_trans (mul_add _ _ _) (add_congr (mul_congr (equiv_refl _) (mul_comm _ _)) (equiv_refl _))))

theorem Compatible.physical_entropy_correction {grouping : FiniteGibbsGrouping micro groups features} {original : FiniteGibbsFamily micro features}
    (compatible : grouping.Compatible original) (parameters : Fin features → ConstructiveReal) (boltzmann : PositiveRatio) :
    Equiv (statisticalEntropy boltzmann (original.entropy parameters))
      (add (statisticalEntropy boltzmann (grouping.macroFamily.entropy parameters))
        (mul (ofSignedRatio boltzmann.toSignedRatio) (grouping.macroFamily.expectation parameters grouping.macroFamily.logReference))) :=
  equiv_trans (mul_congr (equiv_refl _) (mul_congr (equiv_refl _)
    (FiniteGibbsTilt.entropy_congr (compatible.logWeight parameters)))) (grouping.physical_entropy_correction parameters boltzmann)

end Thesis.Probability.FiniteGibbsGrouping
