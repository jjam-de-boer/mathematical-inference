import Thesis.Probability.ConstructiveRealReciprocal
import Thesis.Probability.ConstructiveRealLogMultiplication

namespace Thesis.Probability
open ConstructiveReal

/-- Explicit physical temperature calibration for a positive Boltzmann
constant. Supplying a physical temperature and interpreting the resulting
multiplier as inverse thermal energy is an additional physical input.
The calibration does not define thermodynamic entropy or prove empirical
adequacy of the finite state model. -/
structure ThermalCalibration (boltzmann : PositiveRatio) where
  temperature : ConstructiveReal
  lower : PositiveRatio
  positive : LE (ofSignedRatio lower.toSignedRatio) temperature

namespace ThermalCalibration

def thermalEnergy {boltzmann : PositiveRatio} (calibration : ThermalCalibration boltzmann) : ConstructiveReal :=
  mul (ofSignedRatio boltzmann.toSignedRatio) calibration.temperature

theorem thermalEnergy_positive {boltzmann : PositiveRatio} (calibration : ThermalCalibration boltzmann) :
    LE (ofSignedRatio (boltzmann.mul calibration.lower).toSignedRatio) calibration.thermalEnergy :=
  mul_positive_lower _ _ boltzmann calibration.lower (le_refl _) calibration.positive

def beta {boltzmann : PositiveRatio} (calibration : ThermalCalibration boltzmann) : ConstructiveReal :=
  calibration.thermalEnergy.positiveInverse (boltzmann.mul calibration.lower) calibration.thermalEnergy_positive

def inverseTemperature {boltzmann : PositiveRatio} (calibration : ThermalCalibration boltzmann) : ConstructiveReal :=
  calibration.temperature.positiveInverse calibration.lower calibration.positive

/-- The chosen inverse-energy multiplier obeys kB*beta = 1/T, proved using
the actual positive reciprocal and its normalization equation. -/
theorem boltzmann_beta {boltzmann : PositiveRatio} (calibration : ThermalCalibration boltzmann) :
    Equiv (mul (ofSignedRatio boltzmann.toSignedRatio) calibration.beta) calibration.inverseTemperature := by
  apply inverse_unique calibration.temperature
  · exact equiv_trans (equiv_symm (mul_assoc _ _ _))
      (equiv_trans (mul_congr (mul_comm _ _) (equiv_refl _))
        (calibration.thermalEnergy.mul_positiveInverse (boltzmann.mul calibration.lower) calibration.thermalEnergy_positive))
  · exact calibration.temperature.mul_positiveInverse calibration.lower calibration.positive

end ThermalCalibration
end Thesis.Probability
