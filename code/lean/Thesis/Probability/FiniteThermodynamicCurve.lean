import Thesis.Probability.FiniteGibbsCurveVariation
import Thesis.Probability.FiniteThermodynamicIdentification

/-!
# Thermodynamic comparison along general finite probability curves

Probability regularity is supplied quantitatively and the statistical entropy
remainder is derived from it. Equilibrium, temperature calibration and an
independent thermodynamic Clausius law remain explicit physical hypotheses.
Current energy levels may vary; their probability contribution is heat, with
the separate level-variation work term proved by `FiniteEnergyVariation`.
The declared model fixes the microstate indices and particle counts; `levels`
supplies current analytic energies in place of the model's fixed energy data.
-/

namespace Thesis.Probability.FiniteStatisticalMechanics
open ConstructiveReal

/-- Canonical Gibbs law at the current energy levels. The level functions
need no derivative for the entropy--heat identity; mean-energy variation
separately includes their work contribution whenever such derivatives exist. -/
def canonicalCurveFamily (model : FinitePhysicalModel states)
    (levels : Fin states → ConstructiveReal → ConstructiveReal) (t : ConstructiveReal) : FiniteGibbsTilt states :=
  ⟨model.nonempty, (fun _ => zero), (fun i => levels i t)⟩

/-- The computed uniform Clausius variation for an arbitrary quantitatively
regular probability path of canonical states. Energies and temperature may
change, and the probability path need not be affine. -/
def canonicalCurve_clausius (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (curve : RegularProbabilityCurve states domain) (levels : Fin states → ConstructiveReal → ConstructiveReal)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann)
    (atEquilibrium : ∀ t hx i, Equiv (curve.mass i t)
      ((canonicalCurveFamily model levels t).mass (calibration t hx).beta i)) :
    UniformDerivativeWithin domain (fun t hx => statisticalEntropy boltzmann (curve.entropy t hx))
      (fun t hx => mul (calibration t hx).inverseTemperature
        (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) (fun i => levels i t))) := by
  let derivative := curve.gibbsEntropy_uniformDerivative (fun t _ => canonicalCurveFamily model levels t)
    (fun t hx => (calibration t hx).beta) atEquilibrium
  have rate (t : ConstructiveReal) (hx : domain t) : Equiv
      (sub (mul (calibration t hx).beta (FiniteLinear.pair states (fun i => curve.velocity i t) (canonicalCurveFamily model levels t).energy))
        (FiniteLinear.pair states (fun i => curve.velocity i t) (canonicalCurveFamily model levels t).offset))
      (mul (calibration t hx).beta (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) (fun i => levels i t))) :=
    equiv_trans (add_congr (equiv_refl _) (neg_congr (FiniteLinear.pair_zero_second states _)))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _))
  exact (statisticalEntropy_uniformDerivative boltzmann (derivative.slope_congr rate)).slope_congr (fun t hx =>
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (mul_congr (calibration t hx).boltzmann_beta (equiv_refl _)))

/-- An independently characterized closed-system thermodynamic entropy
agrees with the actual statistical entropy up to its reference constant on
any admitted interval of the general regular curve. Fixed particle count,
equilibrium and calibrated temperature are explicit. Uniformity is proved
for the statistical side, rather than inferred from pointwise smoothness. -/
theorem canonicalCurve_thermodynamic_agreement (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (particleCount : Nat) (_closed : ∀ i, model.particles i = particleCount)
    (curve : RegularProbabilityCurve states domain) (levels : Fin states → ConstructiveReal → ConstructiveReal)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann)
    (atEquilibrium : ∀ t hx i, Equiv (curve.mass i t)
      ((canonicalCurveFamily model levels t).mass (calibration t hx).beta i))
    (thermodynamic : ∀ t, domain t → ConstructiveReal)
    (clausius : UniformDerivativeWithin domain thermodynamic (fun t hx => mul (calibration t hx).inverseTemperature
      (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) (fun i => levels i t))))
    (a b constant : ConstructiveReal) (ordered : LE a b)
    (admitted : ∀ t, LE a t → LE t b → domain t)
    (reference : Equiv (thermodynamic a (admitted a (le_refl a) ordered))
      (add (statisticalEntropy boltzmann (curve.entropy a (admitted a (le_refl a) ordered))) constant)) :
    Equiv (thermodynamic b (admitted b ordered (le_refl b)))
      (add (statisticalEntropy boltzmann (curve.entropy b (admitted b ordered (le_refl b)))) constant) :=
  clausius.agreement_of_reference_on_interval (canonicalCurve_clausius model boltzmann curve levels calibration atEquilibrium)
    (fun _ _ => equiv_refl _) a b constant ordered admitted reference

end Thesis.Probability.FiniteStatisticalMechanics
