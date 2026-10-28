import Thesis.Probability.FinitePhysicalEnsembles
import Thesis.Probability.FiniteThermalCalibration
import Thesis.Probability.FiniteEnergyVariation
import Thesis.Probability.FiniteGibbsEntropyVariation

namespace Thesis.Probability.FiniteStatisticalMechanics
open ConstructiveReal
open Distros.RationalLinear

/-- Statistical physical entropy in calibrated units: S_G = kB*ln(2)*H_bits.
This definition is not an identification with an independently characterized
thermodynamic entropy; that requires separate physical hypotheses. -/
def statisticalEntropy (boltzmann : PositiveRatio) (bits : ConstructiveReal) : ConstructiveReal :=
  mul (ofSignedRatio boltzmann.toSignedRatio) (mul lnTwo bits)

/-- The unit conversion acts on the actual entropy derivative and retains
its computed error modulus. -/
def statisticalEntropy_hasDerivativeAt (boltzmann : PositiveRatio) (bits : ConstructiveReal → ConstructiveReal)
    (point naturalRate : ConstructiveReal)
    (derivative : HasDerivativeAt (fun t => mul (bits t) lnTwo) point naturalRate) :
    HasDerivativeAt (fun t => statisticalEntropy boltzmann (bits t)) point (mul (ofSignedRatio boltzmann.toSignedRatio) naturalRate) :=
  ((derivative.mul_constant (ofSignedRatio boltzmann.toSignedRatio)).function_congr (fun t =>
    equiv_trans (mul_comm _ _) (mul_congr (equiv_refl _) (mul_comm _ _)))).slope_congr (mul_comm _ _)

/-- Clausius variation at a canonically distributed state, for any actual
normalized differentiable probability path. Heat is the probability-change
part of mean-energy variation. Energy levels may also vary; their work term
is kept separate by `FiniteEnergyVariation.meanEnergy_hasDerivativeAt`. A closed
physical canonical interpretation uses `Sector.canonicalModel` to fix particle
number; the variation identity itself is mathematical. -/
def canonical_clausius (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (calibration : ThermalCalibration boltzmann)
    (path : Fin states → ConstructiveReal → UnitIntervalValue) (point : ConstructiveReal)
    (velocity : Fin states → ConstructiveReal)
    (derivatives : ∀ i, HasDerivativeAt (fun t => (path i t).value) point (velocity i))
    (normalized : ∀ t, Equiv (realDot states (fun _ => 1) (fun i => (path i t).value)) one)
    (atEquilibrium : ∀ i, Equiv (path i point).value (model.canonical.mass calibration.beta i)) :
    HasDerivativeAt (fun t => statisticalEntropy boltzmann (realEntropySum ((List.finRange states).map (fun i => path i t)))) point
      (mul calibration.inverseTemperature (FiniteEnergyVariation.heatRate velocity model.energyValue)) := by
  let heat := FiniteEnergyVariation.heatRate velocity model.energyValue
  let derivative := model.canonical.entropyCurve_hasDerivativeAt calibration.beta path point velocity derivatives normalized atEquilibrium
  have rate : Equiv (sub (mul calibration.beta heat) (FiniteLinear.pair states velocity (fun _ => zero))) (mul calibration.beta heat) :=
    equiv_trans (add_congr (equiv_refl _) (neg_congr (FiniteLinear.pair_zero_second states velocity)))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero))) (add_zero _))
  exact (statisticalEntropy_hasDerivativeAt boltzmann _ point _ (derivative.slope_congr rate)).slope_congr
    (equiv_trans (equiv_symm (mul_assoc _ _ _)) (mul_congr calibration.boltzmann_beta (equiv_refl _)))

/-- The open-system entropy relation includes the chemical-potential term:
S' = (heatRate - mu*particleRate)/T. Here `heatRate` is the probability
contribution to energy; subtracting chemical exchange gives thermal heat.
The Gibbs particle multiplier is
explicitly calibrated as -beta*mu, and the positive temperature calibration
is separate from the probability and differentiation proofs. -/
def grandCanonical_clausius (model : FinitePhysicalModel states) (boltzmann : PositiveRatio)
    (calibration : ThermalCalibration boltzmann) (mu : ConstructiveReal)
    (path : Fin states → ConstructiveReal → UnitIntervalValue) (point : ConstructiveReal)
    (velocity : Fin states → ConstructiveReal)
    (derivatives : ∀ i, HasDerivativeAt (fun t => (path i t).value) point (velocity i))
    (normalized : ∀ t, Equiv (realDot states (fun _ => 1) (fun i => (path i t).value)) one)
    (atEquilibrium : ∀ i, Equiv (path i point).value
      ((model.grandCanonical calibration.beta (neg (mul calibration.beta mu))).mass one i)) :
    HasDerivativeAt (fun t => statisticalEntropy boltzmann (realEntropySum ((List.finRange states).map (fun i => path i t)))) point
      (mul calibration.inverseTemperature (sub (FiniteEnergyVariation.heatRate velocity model.energyValue)
        (mul mu (FiniteLinear.pair states velocity model.particleValue)))) := by
  let beta := calibration.beta
  let alpha := neg (mul beta mu)
  let family := model.grandCanonical beta alpha
  let heat := FiniteEnergyVariation.heatRate velocity model.energyValue
  let particles := FiniteLinear.pair states velocity model.particleValue
  let derivative := family.entropyCurve_hasDerivativeAt one path point velocity derivatives normalized atEquilibrium
  have offsetZero : Equiv (FiniteLinear.pair states velocity family.offset) zero :=
    equiv_trans (FiniteLinear.pair_congr states velocity velocity _ (fun _ => zero) (fun _ => equiv_refl _)
      (fun i => positiveLn_one PositiveRatio.one (le_refl one))) (FiniteLinear.pair_zero_second states velocity)
  have score : Equiv (FiniteLinear.pair states velocity family.energy) (add (mul beta heat) (mul alpha particles)) :=
    equiv_trans (FiniteLinear.pair_comm states _ _) (equiv_trans (model.grand_score_pair beta alpha velocity)
      (add_congr (mul_congr (equiv_refl _) (FiniteLinear.pair_comm states _ _))
        (mul_congr (equiv_refl _) (FiniteLinear.pair_comm states _ _))))
  have rate : Equiv (sub (mul one (FiniteLinear.pair states velocity family.energy)) (FiniteLinear.pair states velocity family.offset))
      (mul beta (sub heat (mul mu particles))) :=
    equiv_trans (add_congr (equiv_trans (one_mul _) score) (neg_congr offsetZero))
      (equiv_trans (add_congr (equiv_refl _) (equiv_symm (ofSignedRatio_neg SignedRatio.zero)))
        (equiv_trans (add_zero _) (equiv_trans (add_congr (equiv_refl _)
          (equiv_trans (neg_mul _ _) (neg_congr (mul_assoc _ _ _)))) (equiv_symm (mul_sub _ _ _)))))
  exact (statisticalEntropy_hasDerivativeAt boltzmann _ point _ (derivative.slope_congr rate)).slope_congr
    (equiv_trans (equiv_symm (mul_assoc _ _ _)) (mul_congr calibration.boltzmann_beta (equiv_refl _)))

end Thesis.Probability.FiniteStatisticalMechanics
