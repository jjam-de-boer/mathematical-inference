import Thesis.Probability.FiniteStatisticalEntropy
import Thesis.Probability.ConstructiveRealLogInverse

namespace Thesis.Examples.FiniteStatisticalMechanics
open Probability Probability.Distros ConstructiveReal
open Probability.Distros.RationalLinear
open Probability.FinitePhysicalModel

private def shellModel : FinitePhysicalModel 3 := {
  nonempty := by decide
  energy i := if i = 0 then SignedRatio.zero else if i = 1 then ⟨1, 2, by decide⟩ else ⟨2, 4, by decide⟩
  particles _ := 1 }
private def shell := shellModel.all.closedShell (⟨1, 2, by decide⟩ : SignedRatio) 1 ⟨1, by decide +kernel⟩ (by decide +kernel) (by decide +kernel)

example : shellModel.all.microcanonical (⟨1, 2, by decide⟩ : SignedRatio) 1
    ⟨1, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) = shell.uniform := rfl

/-- Equal-energy states remain distinct, including unreduced energies. -/
example : shell.cells = [(1 : Fin 3), 2] := by decide +kernel
example : QProb.Equiv (shell.uniform.pmf (1 : Fin 3)) (⟨1, 2, by decide⟩ : QProb) := by decide +kernel
example : QProb.Equiv (shell.uniform.pmf (2 : Fin 3)) (⟨1, 2, by decide⟩ : QProb) := by decide +kernel
example : (shell.uniform.pmf (0 : Fin 3)).num = 0 := by decide +kernel

private def presentation : Distro (Fin 3) := ⟨⟨[(1, 1), (1, 1), (2, 2), (0, 0)], 4, by decide, by decide +kernel⟩⟩
private theorem presentation_same : presentation.SameLaw shell.uniform :=
  presentation.sameLaw_of_pmf shell.uniform (by decide +kernel)
private theorem presentation_support : presentation.AlmostSurely (fun i => i ∈ shell.cells) := by
  intro atom member positive
  change atom ∈ [((1 : Fin 3), 1), (1, 1), (2, 2), (0, 0)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact False.elim ((Nat.lt_irrefl 0) positive)

/-- Splitting a record atom and adding a null outlier do not manufacture
physical degeneracy or change the microcanonical entropy. -/
example : ExactLog.Equiv (presentation.entropy shell.grid presentation_support)
    (shell.uniform.entropy shell.grid shell.uniform_support) :=
  Distro.entropy_sameLaw presentation_same shell.grid presentation_support shell.uniform_support

example : presentation.SameLaw shell.uniform := shell.uniform_unique presentation presentation_support
  (Distro.entropy_sameLaw presentation_same shell.grid presentation_support shell.uniform_support)

private def binary : FinitePhysicalModel 2 := {
  nonempty := by decide
  energy i := if i = 0 then SignedRatio.zero else SignedRatio.one
  particles _ := 1 }
private def openBinary : FinitePhysicalModel 2 := {
  nonempty := by decide
  energy := binary.energy
  particles i := if i = 0 then 0 else 1 }
/-- The computed canonical sector fixes particle number and preserves both
closed-system microstates. -/
private def closedSector := binary.all.particleShell 1 ⟨0, by decide +kernel⟩ (by decide +kernel)
example : closedSector.cells = [(0 : Fin 2), 1] := by decide +kernel
example (i : Fin closedSector.cells.length) :
    (binary.all.canonicalModel 1 ⟨0, by decide +kernel⟩ (by decide +kernel)).particles i = 1 :=
  binary.all.canonicalModel_particles 1 ⟨0, by decide +kernel⟩ (by decide +kernel) i

private def half : SignedRatio := ⟨1, 2, by decide⟩
private def third : SignedRatio := ⟨1, 3, by decide⟩
private def twoThirds : SignedRatio := ⟨2, 3, by decide⟩
private def threeHalves : SignedRatio := ⟨3, 2, by decide⟩
private def two : PositiveRatio := .ofNat 2 (by decide)

private theorem exp_lnTwo : Equiv lnTwo.exp (ofSignedRatio two.toSignedRatio) :=
  equiv_trans (exp_congr (equiv_symm (positiveLn_two two (le_refl _)))) (exp_positiveLn _ two (le_refl _))
private theorem exp_neg_lnTwo : Equiv (neg lnTwo).exp (ofSignedRatio half) :=
  inverse_unique (ofSignedRatio two.toSignedRatio) _ _
    (equiv_trans (mul_congr (equiv_symm exp_lnTwo) (equiv_refl _)) (exp_mul_exp_neg lnTwo))
    (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))

private theorem weight0 : Equiv (binary.canonical.weight lnTwo (0 : Fin 2)) one := by
  have logarithm : Equiv (binary.canonical.logWeight lnTwo (0 : Fin 2)) zero :=
    equiv_trans (add_zero _) (equiv_trans (mul_neg _ _) (equiv_trans (neg_congr (mul_zero _))
      (equiv_symm (ofSignedRatio_neg SignedRatio.zero))))
  exact equiv_trans (exp_congr logarithm) exp_zero
private theorem weight1 : Equiv (binary.canonical.weight lnTwo (1 : Fin 2)) (ofSignedRatio half) :=
  equiv_trans (exp_congr (equiv_trans (add_zero _) (equiv_trans (mul_neg _ _) (neg_congr (mul_one _))))) exp_neg_lnTwo

private theorem partition_exact : Equiv (binary.canonical.partition lnTwo) (ofSignedRatio threeHalves) := by
  change Equiv (add (binary.canonical.weight lnTwo 0) (add (binary.canonical.weight lnTwo 1) zero)) _
  exact equiv_trans (add_congr weight0 (equiv_trans (add_congr weight1 (equiv_refl _)) (add_zero _)))
    (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))
private theorem inverse_exact : Equiv (binary.canonical.partitionInverse lnTwo) (ofSignedRatio twoThirds) :=
  inverse_unique (binary.canonical.partition lnTwo) _ _
    ((binary.canonical.partition lnTwo).mul_positiveInverse _ (binary.canonical.partition_positive lnTwo))
    (equiv_trans (mul_congr partition_exact (equiv_refl _))
      (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))
private theorem mass0 : Equiv (binary.canonical.mass lnTwo (0 : Fin 2)) (ofSignedRatio twoThirds) :=
  equiv_trans (mul_congr weight0 inverse_exact) (one_mul _)
private theorem mass1 : Equiv (binary.canonical.mass lnTwo (1 : Fin 2)) (ofSignedRatio third) :=
  equiv_trans (mul_congr weight1 inverse_exact)
    (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)))
private theorem energy_indicator (i : Fin 2) : Equiv (binary.energyValue i) (realInteger (if i = 1 then 1 else 0)) := by
  have cases := (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i
  rcases cases with rfl | rfl <;> exact equiv_refl _
private theorem mean_exact : Equiv (binary.canonical.expectation lnTwo binary.energyValue) (ofSignedRatio third) :=
  equiv_trans (FiniteLinear.pair_congr 2 _ _ _ _ energy_indicator (fun _ => equiv_refl _))
    (equiv_trans (FiniteLinear.pair_unit 2 1 _) mass1)

/-- The actual nonuniform canonical law maximizes entropy at mean 1/3.
The optimum is established by the Gibbs theorem, not assumed by the fixture. -/
example (observed : Fin 2 → UnitIntervalValue)
    (normalized : Equiv (realDot 2 (fun _ => 1) (fun i => (observed i).value)) one)
    (energy : Equiv (FiniteLinear.pair 2 binary.energyValue (fun i => (observed i).value)) (ofSignedRatio third)) :
    LE (realEntropySum ((List.finRange 2).map observed)) (binary.canonical.entropy lnTwo) :=
  binary.canonical_maximal lnTwo observed normalized (equiv_trans energy (equiv_symm mean_exact))

/-- E=N for this model. Chemical potential one cancels the energy score,
checking the grand-canonical sign convention on actual physical observables. -/
example (beta : ConstructiveReal) (i : Fin 2) : Equiv
    (openBinary.grandFamily.score (grandParameters beta (neg (mul beta one))) i) zero := by
  have equal : Equiv (openBinary.energyValue i) (openBinary.particleValue i) := by
    have cases := (by decide +kernel : ∀ j : Fin 2, j = 0 ∨ j = 1) i
    rcases cases with rfl | rfl <;> exact equiv_refl _
  exact equiv_trans (openBinary.grand_chemical_score beta one i) (equiv_trans
    (mul_congr (equiv_refl _) ((sub_equiv_zero_iff _ _).mpr (equiv_trans equal (equiv_symm (one_mul _))))) (mul_zero _))

/-- With kB=1 and T=2, the constructed inverse thermal-energy multiplier
is independently recovered as 1/2. -/
private def calibration : ThermalCalibration PositiveRatio.one :=
  ⟨ofSignedRatio two.toSignedRatio, two, le_refl _⟩
example : Equiv calibration.beta (ofSignedRatio half) :=
  inverse_unique calibration.thermalEnergy _ _
    (calibration.thermalEnergy.mul_positiveInverse _ calibration.thermalEnergy_positive)
    (equiv_trans (mul_congr (one_mul _) (equiv_refl _))
      (equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))

private def quarter : SignedRatio := ⟨1, 4, by decide⟩
private def velocity (i : Fin 2) : ConstructiveReal := ofSignedRatio (if i = 0 then quarter else SignedRatio.neg quarter)
private def probability (i : Fin 2) (t : ConstructiveReal) : ConstructiveReal := affineCoordinate (ofSignedRatio half) (velocity i) t
private def levelSlope (i : Fin 2) : ConstructiveReal := if i = 0 then zero else one
private def levels (i : Fin 2) (t : ConstructiveReal) : ConstructiveReal := affineCoordinate (levelSlope i) (levelSlope i) t
private abbrev Expression := RationalPolynomial.Expression 0
private def heatExpr : Expression := .add (.mul (.constant quarter) (.constant SignedRatio.zero))
  (.add (.mul (.constant (SignedRatio.neg quarter)) (.constant SignedRatio.one)) (.constant SignedRatio.zero))
private def workExpr : Expression := .add (.mul (.constant half) (.constant SignedRatio.zero))
  (.add (.mul (.constant half) (.constant SignedRatio.one)) (.constant SignedRatio.zero))

private theorem heat_exact : Equiv (FiniteEnergyVariation.heatRate velocity (fun i => levels i zero)) (ofSignedRatio (SignedRatio.neg quarter)) :=
  equiv_trans (FiniteLinear.pair_congr 2 velocity velocity _ _ (fun _ => equiv_refl _) (fun i => affineCoordinate_zero _ _))
    (RationalPolynomial.Expression.equalityCheck_sound_real heatExpr (.constant (SignedRatio.neg quarter)) (by decide +kernel) (fun i => Fin.elim0 i))
private theorem work_exact : Equiv (FiniteEnergyVariation.workRate (fun i => probability i zero) levelSlope) (ofSignedRatio half) :=
  equiv_trans (FiniteLinear.pair_congr 2 _ _ levelSlope levelSlope (fun i => affineCoordinate_zero _ _) (fun _ => equiv_refl _))
    (RationalPolynomial.Expression.equalityCheck_sound_real workExpr (.constant half) (by decide +kernel) (fun i => Fin.elim0 i))

/-- A local affine probability/level variation has heat -1/4 and work 1/2,
so its actual mean-energy derivative is independently recovered as 1/4. -/
example : HasDerivativeAt (FiniteEnergyVariation.meanEnergy probability levels) zero (ofSignedRatio quarter) :=
  (FiniteEnergyVariation.meanEnergy_hasDerivativeAt probability levels zero velocity levelSlope
    (fun i => HasDerivativeAt.affine zero (velocity i) (ofSignedRatio half))
    (fun i => HasDerivativeAt.affine zero (levelSlope i) (levelSlope i))).slope_congr
    (equiv_trans (add_congr heat_exact work_exact)
      (equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))))

end Thesis.Examples.FiniteStatisticalMechanics
