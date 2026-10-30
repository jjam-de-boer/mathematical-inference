import Thesis.Examples.BinaryGibbsCurve
import Thesis.Probability.FiniteGrandThermodynamicCurve

namespace Thesis.Examples.ThermodynamicGibbsCurve
open Probability ConstructiveReal
open Probability.FiniteStatisticalMechanics
open BinaryGibbsCurve

private def half : PositiveRatio := ⟨1, 2, by decide, by decide⟩
private def twoRatio : PositiveRatio := .ofNat 2 (by decide)
private def temperature (t : ConstructiveReal) (inside : domain t) : ConstructiveReal :=
  t.positiveInverse PositiveRatio.one inside.1
private theorem temperature_positive (t : ConstructiveReal) (inside : domain t) :
    LE (ofSignedRatio half.toSignedRatio) (temperature t inside) :=
  (le_congr (ofPositiveRatio_inverse twoRatio twoRatio (le_refl two)) (equiv_refl _)).mp
    (positiveInverse_antitone t two PositiveRatio.one twoRatio inside.1 (le_refl two) inside.2)
private def calibration (t : ConstructiveReal) (inside : domain t) : ThermalCalibration PositiveRatio.one :=
  ⟨temperature t inside, half, temperature_positive t inside⟩

/-- With kB=1 and the actual temperature T=1/t, the calibration's computed
inverse-energy multiplier is proved equal to the Gibbs parameter t. -/
private theorem beta_eq (t : ConstructiveReal) (inside : domain t) : Equiv (calibration t inside).beta t := by
  let current := calibration t inside
  have normalized : Equiv (mul current.thermalEnergy t) one :=
    equiv_trans (mul_congr (one_mul _) (equiv_refl _))
      (equiv_trans (mul_comm _ _) (t.mul_positiveInverse PositiveRatio.one inside.1))
  exact inverse_unique current.thermalEnergy current.beta t
    (current.thermalEnergy.mul_positiveInverse _ current.thermalEnergy_positive) normalized
private theorem inverseTemperature_eq (t : ConstructiveReal) (inside : domain t) :
    Equiv (calibration t inside).inverseTemperature t :=
  equiv_trans (equiv_symm (calibration t inside).boltzmann_beta)
    (equiv_trans (one_mul _) (beta_eq t inside))
private def levels (i : Fin 2) (_ : ConstructiveReal) : ConstructiveReal := model.energyValue i
private theorem equilibrium (t : ConstructiveReal) (inside : domain t) (i : Fin 2) :
    Equiv (curve.mass i t) ((canonicalCurveFamily model levels t).mass (calibration t inside).beta i) := by
  have logs (j : Fin 2) : Equiv (model.canonical.logWeight t j)
      ((canonicalCurveFamily model levels t).logWeight (calibration t inside).beta j) :=
    add_congr (mul_congr (equiv_symm (beta_eq t inside)) (equiv_refl (neg (model.energyValue j)))) (equiv_refl zero)
  exact equiv_trans (curve_is_gibbs t i) (FiniteGibbsTilt.mass_congr
    (first := model.canonical) (second := canonicalCurveFamily model levels t)
    (left := t) (right := (calibration t inside).beta) logs i)

/-- A genuine varying Gibbs path satisfies the derived uniform Clausius law.
The path's exponential/reciprocal regularity was proved in BinaryGibbsCurve;
no entropy or heat derivative certificate is supplied as a premise. -/
example : UniformDerivativeWithin domain
    (fun t hx => statisticalEntropy PositiveRatio.one (curve.entropy t hx))
    (fun t _ => mul t (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) model.energyValue)) :=
  (canonicalCurve_clausius model PositiveRatio.one curve levels calibration equilibrium).slope_congr
    (fun t hx => mul_congr (inverseTemperature_eq t hx) (equiv_refl _))

private theorem one_le_two : LE one two := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
/-- An independent thermodynamic potential with the calibrated Clausius
variation and one reference value agrees at the other end of this actual
nonlinear Gibbs path. It is not defined to equal statistical entropy. -/
example (thermodynamic : ∀ t, domain t → ConstructiveReal)
    (clausius : UniformDerivativeWithin domain thermodynamic
      (fun t _ => mul t (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) model.energyValue)))
    (constant : ConstructiveReal)
    (reference : Equiv (thermodynamic one ⟨le_refl one, one_le_two⟩)
      (add (statisticalEntropy PositiveRatio.one (curve.entropy one ⟨le_refl one, one_le_two⟩)) constant)) :
    Equiv (thermodynamic two ⟨one_le_two, le_refl two⟩)
      (add (statisticalEntropy PositiveRatio.one (curve.entropy two ⟨one_le_two, le_refl two⟩)) constant) :=
  canonicalCurve_thermodynamic_agreement model PositiveRatio.one 1 (fun _ => rfl) curve levels calibration equilibrium
    thermodynamic (clausius.slope_congr (fun t hx => mul_congr (equiv_symm (inverseTemperature_eq t hx)) (equiv_refl _)))
    one two constant one_le_two (fun _ above below => ⟨above, below⟩) reference

/-- A genuinely open physical model: excited-state energy two and particle
number one. Chemical potential one leaves effective energy one, so its
actual grand-canonical law is the same varying binary probability curve. -/
private def openModel : FinitePhysicalModel 2 := {
  nonempty := by decide
  energy i := if i = 0 then SignedRatio.zero else ⟨2, 1, by decide⟩
  particles i := if i = 0 then 0 else 1 }
private def openLevels (i : Fin 2) (_ : ConstructiveReal) : ConstructiveReal := openModel.energyValue i
private theorem effectiveEnergy (i : Fin 2) : Equiv
    (sub (openModel.energyValue i) (mul one (openModel.particleValue i))) (model.energyValue i) := by
  have numeric := (by decide +kernel : ∀ j : Fin 2, SignedRatio.Equiv
    (SignedRatio.sub (openModel.energy j) ⟨(openModel.particles j : Int), 1, by decide⟩) (model.energy j)) i
  exact equiv_trans (add_congr (equiv_refl _) (neg_congr (one_mul _)))
    (equiv_trans (ofSignedRatio_sub _ _) ((ofSignedRatio_equiv_iff _ _).mpr numeric))
private theorem openEquilibrium (t : ConstructiveReal) (inside : domain t) (i : Fin 2) :
    Equiv (curve.mass i t) ((grandCurveFamily openModel openLevels (calibration t inside).beta one t).mass one i) := by
  let family := grandCurveFamily openModel openLevels (calibration t inside).beta one t
  have logs (j : Fin 2) : Equiv (model.canonical.logWeight t j) (family.logWeight one j) := by
    have score : Equiv (family.energy j) (mul t (model.energyValue j)) :=
      mul_congr (beta_eq t inside) (effectiveEnergy j)
    have right : Equiv (family.logWeight one j) (neg (mul t (model.energyValue j))) :=
      equiv_trans (add_congr (one_mul _) (equiv_refl zero)) (equiv_trans (add_zero _) (neg_congr score))
    exact equiv_trans (equiv_trans (add_zero _) (mul_neg _ _)) (equiv_symm right)
  exact equiv_trans (curve_is_gibbs t i) (FiniteGibbsTilt.mass_congr
    (first := model.canonical) (second := family) (left := t) (right := one) logs i)
private theorem thermalRate (t : ConstructiveReal) : Equiv
    (sub (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) openModel.energyValue)
      (mul one (FiniteLinear.pair 2 (fun i => curve.velocity i t) openModel.particleValue)))
    (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) model.energyValue) := by
  let velocity := fun i => curve.velocity i t
  have difference : Equiv (FiniteLinear.pair 2 velocity
      (fun i => sub (openModel.energyValue i) (mul one (openModel.particleValue i))))
      (sub (FiniteLinear.pair 2 velocity openModel.energyValue) (mul one (FiniteLinear.pair 2 velocity openModel.particleValue))) :=
    equiv_trans (FiniteLinear.pair_sub_second 2 velocity _ _)
      (add_congr (equiv_refl _) (neg_congr (FiniteLinear.pair_scale_second 2 one velocity openModel.particleValue)))
  exact equiv_trans (equiv_symm difference) (FiniteLinear.pair_congr 2 velocity velocity _ model.energyValue
    (fun _ => equiv_refl _) effectiveEnergy)

/-- With nonzero chemical potential, the independently computed thermal
probability contribution is 2*dP(excited)-dP(excited), not the full energy
contribution. The derived grand-canonical law recovers the same entropy rate
as the closed binary model after this actual chemical correction. -/
example : UniformDerivativeWithin domain
    (fun t hx => statisticalEntropy PositiveRatio.one (curve.entropy t hx))
    (fun t _ => mul t (FiniteEnergyVariation.heatRate (fun i => curve.velocity i t) model.energyValue)) :=
  (grandCanonicalCurve_clausius openModel PositiveRatio.one curve openLevels calibration (fun _ _ => one) openEquilibrium).slope_congr
    (fun t hx => mul_congr (inverseTemperature_eq t hx) (thermalRate t))

end Thesis.Examples.ThermodynamicGibbsCurve
