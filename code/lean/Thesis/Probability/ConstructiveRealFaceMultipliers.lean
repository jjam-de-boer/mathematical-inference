import Thesis.Probability.ConstructiveRealSupportFace
import Thesis.Probability.ConstructiveRealGibbsSupport
import Thesis.Probability.ConstructiveRealEntropyInterior

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal
open RationalLinear

private def integerRow (row : Inequality variables) : RationalConstraint variables :=
  ⟨fun i => ⟨row.coefficients i, 1, by decide⟩, row.bound⟩

private theorem integerRow_real (row : Inequality variables) (values : Fin variables → ConstructiveReal) :
    (integerRow row).RealHolds values ↔ row.RealHolds values :=
  le_congr (equiv_trans (realRationalDot_pair variables (integerRow row).coefficients values)
    (equiv_symm (FiniteLinear.realDot_pair variables row.coefficients values))) (equiv_refl _)

/-- The existing ideal moment problem, with only the declared expectation
rows passed to the multiplier problem. Simplex normalization and coordinate
nonnegativity remain in the probability domain; adding their coordinate
rows here would trivialize the multiplier row-space condition. -/
def analyticProblem (problem : PartialMomentProblem A) : RationalEntropyProblem problem.cells.length :=
  ⟨problem.nonempty, (problem.intervals.flatMap (fun constraint => constraint.rows problem.cells problem.default)).map integerRow⟩

/-- Transfer retains every coordinate and original closed row exactly. -/
def RealCompatibleLaw.toRationalLaw {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw) : problem.analyticProblem.RealLaw where
  mass := law.mass
  normalized := law.normalized
  valid row member := by
    obtain ⟨original, listed, same⟩ := List.mem_map.mp member
    cases same
    exact (integerRow_real original _).mpr (law.valid original (List.mem_append_right _ listed))

/-- The reverse transfer introduces no additional support or rank assumption. -/
def RationalLaw.toMomentLaw {problem : PartialMomentProblem A} (law : problem.analyticProblem.RealLaw) : problem.RealCompatibleLaw where
  mass := law.mass
  valid row member := by
    rcases List.mem_append.mp member with simplex | moment
    · exact real_simplex_of_nonnegative _ (fun i => (law.mass i).nonnegative) law.normalized row simplex
    · exact (integerRow_real row _).mp
        (law.valid (integerRow row) (List.mem_map.mpr ⟨row, moment, rfl⟩))

theorem RationalLaw.toMomentLaw_maximal {problem : PartialMomentProblem A} (law : problem.analyticProblem.RealLaw)
    (maximal : law.Maximal) : (RationalLaw.toMomentLaw law).Maximal := fun other => maximal other.toRationalLaw

/-- A fully supported rational compatible law supplies explicit analytic
floors without a comparison of unknown optimum probabilities. -/
def CompatibleLaw.positiveFloors [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.CompatibleLaw)
    (positive : law.distro.GridPositive problem.entropyGrid) (index : Fin problem.cells.length) : PositiveRatio :=
  let mass := law.distro.pmf (problem.cells.getD index.val problem.default)
  ⟨mass.num, mass.den, positive _ (by
    exact (List.getElem_eq_getD problem.default).symm ▸ List.getElem_mem index.isLt), mass.den_pos⟩

theorem CompatibleLaw.positiveFloors_le [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.CompatibleLaw)
    (positive : law.distro.GridPositive problem.entropyGrid) (index : Fin problem.cells.length) :
    LE (ofSignedRatio (law.positiveFloors positive index).toSignedRatio) (law.toReal.toRationalLaw.mass index).value := le_refl _

/-- The automatic support witness, viewed on the computed feasible face. -/
def CompatibleLaw.faceSeed [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw) :
    seed.supportFace.analyticProblem.RealLaw := (seed.toSupportFace seed.supportHull).toReal.toRationalLaw

def CompatibleLaw.faceFloors [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw) :
    Fin seed.supportFace.cells.length → PositiveRatio :=
  (seed.toSupportFace seed.supportHull).positiveFloors seed.supportFace_positive

theorem CompatibleLaw.faceFloors_le [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw)
    (index : Fin seed.supportFace.cells.length) :
    LE (ofSignedRatio (seed.faceFloors index).toSignedRatio) (seed.faceSeed.mass index).value :=
  (seed.toSupportFace seed.supportHull).positiveFloors_le seed.supportFace_positive index

/-- A constructive original-grid maximum obtained by optimizing on the
computed support face and extending by zero. The starting feasible witness
may itself have zeros; no support face or positive law is supplied by the caller. -/
def CompatibleLaw.faceIdeal [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw) : problem.RealCompatibleLaw :=
  (RationalLaw.toMomentLaw seed.faceSeed.maximize).fromSupportFace seed

theorem CompatibleLaw.faceIdeal_maximal [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw) :
    seed.faceIdeal.Maximal :=
  (RationalLaw.toMomentLaw seed.faceSeed.maximize).fromSupportFace_maximal seed
    (RationalLaw.toMomentLaw_maximal seed.faceSeed.maximize seed.faceSeed.maximize_maximal)

/-- On the computed face, actual natural-unit multipliers are fitted from
feasibility. Forced-zero states are absent from this coefficient system;
finite full-grid multipliers are not claimed. Redundant rows are allowed.
For interval rows this remains an all-row representation, not signed KKT. -/
def CompatibleLaw.faceMultipliers [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw) :
    seed.supportFace.analyticProblem.LagrangeCoefficients (fun i =>
      entropyNaturalGradient (seed.faceSeed.maximize.mass i).value
        (RationalEntropyProblem.interiorLower seed.supportFace.cells.length (seed.faceFloors i))
        (seed.faceSeed.maximize_positive seed.faceFloors seed.faceFloors_le i)) :=
  seed.faceSeed.fittedNaturalMultipliers seed.faceFloors seed.faceFloors_le

/-- The normalized Gibbs law holds on the entire computed feasible face,
including for problems that force boundary zeros on their original grid. -/
theorem CompatibleLaw.face_gibbsForm [DecidableEq A] {problem : PartialMomentProblem A} (seed : problem.CompatibleLaw)
    (index : Fin seed.supportFace.cells.length) :
    Equiv (seed.faceSeed.maximize.mass index).value
      (mul (neg (seed.faceMultipliers.score index)).exp seed.faceMultipliers.partitionInverse) :=
  seed.faceSeed.fitted_gibbsForm seed.faceFloors seed.faceFloors_le index

end Thesis.Probability.Distros.PartialMomentProblem
