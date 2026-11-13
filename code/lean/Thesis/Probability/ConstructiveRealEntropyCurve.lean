import Thesis.Probability.ConstructiveRealEntropyFirstVariation
import Thesis.Probability.ConstructiveDerivativeLocalDomain
import Thesis.Probability.ConstructiveDerivativeChain
import Thesis.Probability.ConstructiveRealBilinearFubini
import Thesis.Probability.ConstructiveRealGibbsInequality

namespace Thesis.Probability.ConstructiveReal
open Distros.RationalLinear

/-- Natural Shannon entropy along arbitrary differentiable finite probability
coordinates. Positivity is required only at the evaluation point; computed
local half-floors admit the logarithms. Normalization is a separate hypothesis
for physical applications. No differentiability at zero is claimed. -/
def entropyCurve_hasDerivativeAt (path : Fin states → ConstructiveReal → UnitIntervalValue)
    (point : ConstructiveReal) (velocity : Fin states → ConstructiveReal)
    (derivatives : ∀ i, HasDerivativeAt (fun t => (path i t).value) point (velocity i))
    (lower : Fin states → PositiveRatio)
    (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (path i point).value) :
    HasDerivativeAt (fun t => mul (realEntropySum ((List.finRange states).map (fun i => path i t))) lnTwo) point
      (FiniteLinear.pair states velocity (fun i => entropyNaturalGradient (path i point).value (lower i) (positive i))) := by
  have component (i : Fin states) : HasDerivativeAt (fun t => (path i t).value.naturalEntropyTerm (path i t).nonnegative (path i t).bounded)
      point (mul (velocity i) (entropyNaturalGradient (path i point).value (lower i) (positive i))) := by
    let fixed := (lower i).half
    have inside : entropyPositiveDomain fixed (path i point).value :=
      ⟨positive_half_lower _ _ (lower i) (positive i) (within_refl _ _), (path i point).bounded⟩
    let chained := (derivatives i).chainWithin (naturalEntropyTerm_hasDerivativeWithinAt (path i point).value fixed inside)
    have admitted (t : ConstructiveReal) (close : Within ((derivatives i).positiveRadius (lower i)).toQProb point t) :
        entropyPositiveDomain fixed (path i t).value :=
      ⟨(derivatives i).positive_near (lower i) (positive i) t close, (path i t).bounded⟩
    let total := chained.toLocalTotal (fun t => (path i t).value.naturalEntropyTerm (path i t).nonnegative (path i t).bounded)
      ((derivatives i).positiveRadius (lower i)) admitted (equiv_refl _) (fun _ _ => equiv_refl _)
    exact total.slope_congr (mul_congr (equiv_refl _) (neg_congr (add_congr
      (positiveLn_congr (equiv_refl _) fixed (lower i) inside.1 (positive i)) (equiv_refl _))))
  let summed := HasDerivativeAt.listSum (List.finRange states)
    (fun i t => (path i t).value.naturalEntropyTerm (path i t).nonnegative (path i t).bounded)
    (fun i => mul (velocity i) (entropyNaturalGradient (path i point).value (lower i) (positive i))) point component
  exact summed.function_congr (fun t => by
    simpa only [List.map_map, Function.comp_def] using equiv_symm (realEntropySum_natural ((List.finRange states).map (fun i => path i t))))

/-- A path normalized at every parameter has a zero-sum velocity, derived
by differentiating the actual finite sum and using derivative uniqueness.
A caller need not supply a tangent-space assertion independently. -/
theorem normalized_curve_velocity (path : Fin states → ConstructiveReal → UnitIntervalValue)
    (point : ConstructiveReal) (velocity : Fin states → ConstructiveReal)
    (derivatives : ∀ i, HasDerivativeAt (fun t => (path i t).value) point (velocity i))
    (normalized : ∀ t, Equiv (realDot states (fun _ => 1) (fun i => (path i t).value)) one) :
    Equiv (realDot states (fun _ => 1) velocity) zero := by
  let summed := HasDerivativeAt.listSum (List.finRange states) (fun i t => (path i t).value) velocity point derivatives
  let constant := summed.function_congr (fun t => normalized_mass_sum (fun i => path i t) (normalized t))
  have vanished := constant.unique (HasDerivativeAt.constant point one)
  exact equiv_trans (equiv_trans (FiniteLinear.realDot_pair states (fun _ => 1) velocity)
    (listSum_map_congr (List.finRange states) _ _ (fun i _ => one_mul _))) vanished

end Thesis.Probability.ConstructiveReal
