import Thesis.Probability.FiniteThermodynamicIdentification

namespace Thesis.Probability.FiniteStatisticalMechanics
open ConstructiveReal
open Distros.RationalLinear

/-- Uniform open-system Clausius variation on the admitted affine Gibbs
path. Chemical exchange is subtracted from the probability contribution to
energy: S'=(heatRate-mu*particleRate)/T. The Gibbs particle multiplier is
calibrated explicitly as -beta*mu. -/
def grandCanonicalLine_clausius (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (masses directions : Fin states → ConstructiveReal) (lower : Fin states → PositiveRatio)
    (domain : ConstructiveReal → Prop)
    (positive : ∀ t, domain t → entropyLineDomain masses directions lower t)
    (tangent : Equiv (realDot states (fun _ => 1) directions) zero)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann)
    (chemicalPotential : ∀ t, domain t → ConstructiveReal)
    (atEquilibrium : ∀ t hx i, Equiv (affineCoordinate (masses i) (directions i) t)
      ((model.grandCanonical (calibration t hx).beta (neg (mul (calibration t hx).beta (chemicalPotential t hx)))).mass one i)) :
    UniformDerivativeWithin domain
      (fun t hx => statisticalEntropy boltzmann (entropyLine masses directions lower t (positive t hx)))
      (fun t hx => mul (calibration t hx).inverseTemperature
        (sub (FiniteEnergyVariation.heatRate directions model.energyValue)
          (mul (chemicalPotential t hx) (FiniteLinear.pair states directions model.particleValue)))) := by
  let naturalRate := fun t (hx : domain t) => mul (calibration t hx).beta
    (sub (FiniteEnergyVariation.heatRate directions model.energyValue)
      (mul (chemicalPotential t hx) (FiniteLinear.pair states directions model.particleValue)))
  let base := (naturalEntropyLine_uniformDerivative masses directions lower).restrict domain positive
  have rate (t : ConstructiveReal) (hx : domain t) : Equiv
      (listSum ((List.finRange states).map (fun i => mul (directions i)
        (entropyNaturalGradient (affineCoordinate (masses i) (directions i) t) (lower i) (positive t hx i).1))))
      (naturalRate t hx) := by
    let beta := (calibration t hx).beta
    let mu := chemicalPotential t hx
    let alpha := neg (mul beta mu)
    let family := model.grandCanonical beta alpha
    have gradients := listSum_map_congr (List.finRange states) _ _ (fun i _ => mul_congr (equiv_refl (directions i))
      (neg_congr (add_congr (positiveLn_congr (atEquilibrium t hx i) (lower i) (family.massLower one i)
        (positive t hx i).1 (family.mass_positive one i)) (equiv_refl one))))
    have variation := equiv_trans gradients (family.naturalGradient_pair one directions tangent)
    have offsetZero : Equiv (FiniteLinear.pair states directions family.offset) zero :=
      equiv_trans (FiniteLinear.pair_congr states directions directions _ (fun _ => zero) (fun _ => equiv_refl _)
        (fun _ => positiveLn_one PositiveRatio.one (le_refl one))) (FiniteLinear.pair_zero_second states directions)
    have score := equiv_trans (FiniteLinear.pair_comm states directions family.energy)
      (equiv_trans (model.grand_score_pair beta alpha directions)
        (add_congr (mul_congr (equiv_refl _) (FiniteLinear.pair_comm states _ _))
          (mul_congr (equiv_refl _) (FiniteLinear.pair_comm states _ _))))
    exact equiv_trans variation (equiv_trans (add_congr (equiv_trans (one_mul _) score) (neg_congr offsetZero))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero)))
        (equiv_trans (add_zero _) (equiv_trans (add_congr (equiv_refl _)
          (equiv_trans (neg_mul _ _) (neg_congr (mul_assoc _ _ _)))) (equiv_symm (mul_sub _ _ _))))))
  exact (statisticalEntropy_uniformDerivative boltzmann (base.slope_congr rate)).slope_congr (fun t hx =>
    equiv_trans (equiv_symm (mul_assoc _ _ _)) (mul_congr (calibration t hx).boltzmann_beta (equiv_refl _)))

/-- Conditional agreement with an independently characterized open-system
thermodynamic entropy. Its own Clausius certificate includes the chemical
term and fixes no statistical formula. A reference convention determines
the additive constant after the first variations have been proved equal. -/
theorem grandCanonical_thermodynamic_agreement (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (masses directions : Fin states → ConstructiveReal) (lower : Fin states → PositiveRatio)
    (domain : ConstructiveReal → Prop)
    (positive : ∀ t, domain t → entropyLineDomain masses directions lower t)
    (tangent : Equiv (realDot states (fun _ => 1) directions) zero)
    (calibration : ∀ t, domain t → ThermalCalibration boltzmann)
    (chemicalPotential : ∀ t, domain t → ConstructiveReal)
    (atEquilibrium : ∀ t hx i, Equiv (affineCoordinate (masses i) (directions i) t)
      ((model.grandCanonical (calibration t hx).beta (neg (mul (calibration t hx).beta (chemicalPotential t hx)))).mass one i))
    (thermodynamic : ∀ t, domain t → ConstructiveReal)
    (clausius : UniformDerivativeWithin domain thermodynamic
      (fun t hx => mul (calibration t hx).inverseTemperature
        (sub (FiniteEnergyVariation.heatRate directions model.energyValue)
          (mul (chemicalPotential t hx) (FiniteLinear.pair states directions model.particleValue)))))
    (a b constant : ConstructiveReal) (ordered : LE a b) (width : LE (sub b a) one)
    (admitted : ∀ t, LE a t → LE t b → domain t)
    (reference : Equiv (thermodynamic a (admitted a (le_refl a) ordered))
      (add (statisticalEntropy boltzmann (entropyLine masses directions lower a
        (positive a (admitted a (le_refl a) ordered)))) constant)) :
    Equiv (thermodynamic b (admitted b ordered (le_refl b)))
      (add (statisticalEntropy boltzmann (entropyLine masses directions lower b
        (positive b (admitted b ordered (le_refl b))))) constant) :=
  clausius.agreement_of_reference
    (grandCanonicalLine_clausius model boltzmann masses directions lower domain positive tangent calibration chemicalPotential atEquilibrium)
    (fun _ _ => equiv_refl _) a b constant ordered width admitted reference

end Thesis.Probability.FiniteStatisticalMechanics
