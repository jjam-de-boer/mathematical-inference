import Thesis.Probability.FiniteThermodynamicCurve

namespace Thesis.Probability.FiniteStatisticalMechanics
open ConstructiveReal

/-- Current grand-canonical score beta*(E-mu*N), with fixed declared state
particle counts and potentially changing analytic energy levels. -/
def grandCurveFamily (model : FinitePhysicalModel states) (levels : Fin states → ConstructiveReal → ConstructiveReal)
    (beta mu t : ConstructiveReal) : FiniteGibbsTilt states :=
  ⟨model.nonempty, (fun _ => zero), (fun i => mul beta (sub (levels i t) (mul mu (model.particleValue i))))⟩

private theorem grandCurve_energyPair (model : FinitePhysicalModel states) (levels : Fin states → ConstructiveReal → ConstructiveReal)
    (beta mu t : ConstructiveReal) (velocity : Fin states → ConstructiveReal) :
    Equiv (FiniteLinear.pair states velocity (grandCurveFamily model levels beta mu t).energy)
      (mul beta (sub (FiniteEnergyVariation.heatRate velocity (fun i => levels i t))
        (mul mu (FiniteLinear.pair states velocity model.particleValue)))) :=
  equiv_trans (FiniteLinear.pair_comm states velocity _)
    (equiv_trans (FiniteLinear.pair_scale_first states beta _ velocity)
      (mul_congr (equiv_refl _) (equiv_trans (FiniteLinear.pair_sub_first states _ _ velocity)
        (add_congr (FiniteLinear.pair_comm states _ velocity) (neg_congr
          (equiv_trans (FiniteLinear.pair_scale_first states mu model.particleValue velocity)
            (mul_congr (equiv_refl _) (FiniteLinear.pair_comm states model.particleValue velocity))))))))

/-- Actual uniform open-system Clausius variation along a general regular
curve: S'=(heatRate-mu*particleRate)/T. Only the probability contribution to
energy appears here; any moving-level work remains in the separate first-law
decomposition. No affine path or supplied entropy derivative is assumed. -/
def grandCanonicalCurve_clausius (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (curve : RegularProbabilityCurve states domain) (levels : Fin states → ConstructiveReal → ConstructiveReal)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann) (chemicalPotential : ∀ t, domain t → ConstructiveReal)
    (atEquilibrium : ∀ t hx i, Equiv (curve.mass i t)
      ((grandCurveFamily model levels (calibration t hx).beta (chemicalPotential t hx) t).mass one i)) :
    UniformDerivativeWithin domain (fun t hx => statisticalEntropy boltzmann (curve.entropy t hx))
      (fun t hx => mul (calibration t hx).inverseTemperature
        (sub (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) (fun i => levels i t))
          (mul (chemicalPotential t hx) (FiniteLinear.pair states (fun i => curve.velocity i t) model.particleValue)))) := by
  let family := fun t hx => grandCurveFamily model levels (calibration t hx).beta (chemicalPotential t hx) t
  let derivative := curve.gibbsEntropy_uniformDerivative family (fun _ _ => one) atEquilibrium
  have rate (t : ConstructiveReal) (hx : domain t) : Equiv
      (sub (mul one (FiniteLinear.pair states (fun i => curve.velocity i t) (family t hx).energy))
        (FiniteLinear.pair states (fun i => curve.velocity i t) (family t hx).offset))
      (mul (calibration t hx).beta (sub (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) (fun i => levels i t))
        (mul (chemicalPotential t hx) (FiniteLinear.pair states (fun i => curve.velocity i t) model.particleValue)))) :=
    equiv_trans (add_congr (equiv_trans (one_mul _)
      (grandCurve_energyPair model levels (calibration t hx).beta (chemicalPotential t hx) t _))
      (neg_congr (FiniteLinear.pair_zero_second states _)))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _))
  exact (statisticalEntropy_uniformDerivative boltzmann (derivative.slope_congr rate)).slope_congr (fun t hx =>
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (mul_congr (calibration t hx).boltzmann_beta (equiv_refl _)))

/-- Conditional agreement with independent thermodynamic entropy along a
quantitatively regular open-system probability curve. Chemical exchange,
calibrated temperature, equilibrium and the independent Clausius certificate
are explicit; the statistical certificate is derived from coordinate data.
A reference convention fixes the additive constant. -/
theorem grandCanonicalCurve_thermodynamic_agreement (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (curve : RegularProbabilityCurve states domain) (levels : Fin states → ConstructiveReal → ConstructiveReal)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann) (chemicalPotential : ∀ t, domain t → ConstructiveReal)
    (atEquilibrium : ∀ t hx i, Equiv (curve.mass i t)
      ((grandCurveFamily model levels (calibration t hx).beta (chemicalPotential t hx) t).mass one i))
    (thermodynamic : ∀ t, domain t → ConstructiveReal)
    (clausius : UniformDerivativeWithin domain thermodynamic (fun t hx => mul (calibration t hx).inverseTemperature
      (sub (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) (fun i => levels i t))
        (mul (chemicalPotential t hx) (FiniteLinear.pair states (fun i => curve.velocity i t) model.particleValue)))))
    (a b constant : ConstructiveReal) (ordered : LE a b)
    (admitted : ∀ t, LE a t → LE t b → domain t)
    (reference : Equiv (thermodynamic a (admitted a (le_refl a) ordered))
      (add (statisticalEntropy boltzmann (curve.entropy a (admitted a (le_refl a) ordered))) constant)) :
    Equiv (thermodynamic b (admitted b ordered (le_refl b)))
      (add (statisticalEntropy boltzmann (curve.entropy b (admitted b ordered (le_refl b)))) constant) :=
  clausius.agreement_of_reference_on_interval
    (grandCanonicalCurve_clausius model boltzmann curve levels calibration chemicalPotential atEquilibrium)
    (fun _ _ => equiv_refl _) a b constant ordered admitted reference

end Thesis.Probability.FiniteStatisticalMechanics
