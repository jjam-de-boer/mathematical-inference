import Thesis.Probability.FiniteUniformGibbsVariation
import Thesis.Probability.FiniteStatisticalEntropy
import Thesis.Probability.ConstructivePotentialUniqueness

/-!
# Conditional finite thermodynamic identification

The probability results derive the entropy and equilibrium Gibbs laws. An
independent thermodynamic potential is supplied here with its own uniform
Clausius first-variation certificate. Temperature calibration and equilibrium
are physical hypotheses, not consequences of probability alone.

On an explicitly admitted positive affine probability path, the statistical
entropy certificate is computed from the entropy remainder bounds. Equal
Clausius variations then prove agreement up to an additive reference constant.
This is a conditional identification on this declared path class, not a claim
of empirical adequacy, unrestricted path connectivity, or an inference of
uniform regularity from pointwise smoothness.

Reference: Jaynes, Information Theory and Statistical Mechanics,
Physical Review 106 (1957), 620, doi:10.1103/PhysRev.106.620.
-/

namespace Thesis.Probability.FiniteStatisticalMechanics
open ConstructiveReal
open Distros.RationalLinear

/-- Scaling an actual uniform entropy certificate into physical units. -/
def statisticalEntropy_uniformDerivative {domain : ConstructiveReal → Prop}
    {bits naturalRate : ∀ t, domain t → ConstructiveReal} (boltzmann : PositiveRatio)
    (derivative : UniformDerivativeWithin domain (fun t hx => mul (bits t hx) lnTwo) naturalRate) :
    UniformDerivativeWithin domain (fun t hx => statisticalEntropy boltzmann (bits t hx))
      (fun t hx => mul (ofSignedRatio boltzmann.toSignedRatio) (naturalRate t hx)) :=
  ((derivative.mul_constant (ofSignedRatio boltzmann.toSignedRatio)).function_congr (fun _ _ =>
    equiv_trans (mul_comm _ _) (mul_congr (equiv_refl _) (mul_comm _ _)))).slope_congr (fun _ _ => mul_comm _ _)

/-- Computed uniform Clausius variation for the canonical path. Positivity
is explicit, and the tangent equation supplies normalization of its velocity.
For a closed physical interpretation the state model has fixed particles,
e.g. it is obtained by `Sector.canonicalModel`. -/
def canonicalLine_clausius (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (masses directions : Fin states → ConstructiveReal) (lower : Fin states → PositiveRatio)
    (domain : ConstructiveReal → Prop)
    (positive : ∀ t, domain t → entropyLineDomain masses directions lower t)
    (tangent : Equiv (realDot states (fun _ => 1) directions) zero)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann)
    (atEquilibrium : ∀ t hx i, Equiv (affineCoordinate (masses i) (directions i) t)
      (model.canonical.mass (calibration t hx).beta i)) :
    UniformDerivativeWithin domain
      (fun t hx => statisticalEntropy boltzmann (entropyLine masses directions lower t (positive t hx)))
      (fun t hx => mul (calibration t hx).inverseTemperature (FiniteEnergyVariation.heatRate directions model.energyValue)) := by
  let derivative := model.canonical.entropyLine_uniformDerivative masses directions lower domain positive tangent
    (fun t hx => (calibration t hx).beta) atEquilibrium
  have rate (t : ConstructiveReal) (hx : domain t) :
      Equiv (sub (mul (calibration t hx).beta (FiniteLinear.pair states directions model.canonical.energy))
        (FiniteLinear.pair states directions model.canonical.offset))
        (mul (calibration t hx).beta (FiniteEnergyVariation.heatRate directions model.energyValue)) :=
    equiv_trans (add_congr (equiv_refl _) (neg_congr (FiniteLinear.pair_zero_second states directions)))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _))
  exact (statisticalEntropy_uniformDerivative boltzmann (derivative.slope_congr rate)).slope_congr (fun t hx =>
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (mul_congr (calibration t hx).boltzmann_beta (equiv_refl _)))

/-- Independent thermodynamic entropy and statistical entropy agree up to
the chosen reference constant along an admitted canonical path. The supplied
thermodynamic hypothesis is its Clausius law, not the desired equality.
Particle count is fixed explicitly for the closed-system interpretation.
The path width bound permits the finite rational telescope used in the proof;
longer paths can be handled by finite adjacent intervals. -/
theorem canonical_thermodynamic_agreement (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (particleCount : Nat) (_closed : ∀ i, model.particles i = particleCount)
    (masses directions : Fin states → ConstructiveReal) (lower : Fin states → PositiveRatio)
    (domain : ConstructiveReal → Prop)
    (positive : ∀ t, domain t → entropyLineDomain masses directions lower t)
    (tangent : Equiv (realDot states (fun _ => 1) directions) zero)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann)
    (atEquilibrium : ∀ t hx i, Equiv (affineCoordinate (masses i) (directions i) t)
      (model.canonical.mass (calibration t hx).beta i))
    (thermodynamic : ∀ t, domain t → ConstructiveReal)
    (clausius : UniformDerivativeWithin domain thermodynamic
      (fun t hx => mul (calibration t hx).inverseTemperature (FiniteEnergyVariation.heatRate directions model.energyValue)))
    (a b constant : ConstructiveReal) (ordered : LE a b) (width : LE (sub b a) one)
    (admitted : ∀ t, LE a t → LE t b → domain t)
    (reference : Equiv (thermodynamic a (admitted a (le_refl a) ordered))
      (add (statisticalEntropy boltzmann (entropyLine masses directions lower a
        (positive a (admitted a (le_refl a) ordered)))) constant)) :
    Equiv (thermodynamic b (admitted b ordered (le_refl b)))
      (add (statisticalEntropy boltzmann (entropyLine masses directions lower b
        (positive b (admitted b ordered (le_refl b))))) constant) :=
  clausius.agreement_of_reference
    (canonicalLine_clausius model boltzmann masses directions lower domain positive tangent calibration atEquilibrium)
    (fun _ _ => equiv_refl _) a b constant ordered width admitted reference

end Thesis.Probability.FiniteStatisticalMechanics
