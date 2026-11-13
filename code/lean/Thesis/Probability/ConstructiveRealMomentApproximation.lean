import Thesis.Probability.ConstructiveRealSimplex
import Thesis.Probability.ConstructiveRealEntropySum
import Thesis.Probability.Distros.EntropyMomentConvex

namespace Thesis.Probability.Distros
open ConstructiveReal

/-- Grid realization recovers every specified coordinate, including forced
zeros. Distinct grid labels denote states; record occurrences remain only a
presentation of their law. -/
theorem simplexGrid_pmf [DecidableEq A] (cells : List A) (default : A) (values : Fin cells.length → SignedRatio)
    (simplex : RationalLinear.Simplex values) (nonempty : 0 < cells.length) (distinct : cells.Nodup) (index : Fin cells.length) :
    SignedRatio.Equiv ((simplexGrid cells default values simplex nonempty).pmf (cells.getD index.val default)).toSignedRatio (values index) := by
  let μ := simplexGrid cells default values simplex nonempty
  let target := cells.getD index.val default
  let response := fun cell => if cell = target then (1 : Int) else 0
  have indicator : SignedRatio.Equiv (μ.rationalExpectation (fun cell => ⟨response cell, 1, Nat.zero_lt_one⟩)) (μ.pmf target).toSignedRatio := by
    apply SignedRatio.equiv_trans (μ.rationalExpectation_congr _
      (fun cell => if FiniteProbRecord.singletonEvent target cell then SignedRatio.one else SignedRatio.zero) ?_)
      (μ.rationalExpectation_indicator (FiniteProbRecord.singletonEvent target))
    intro cell
    by_cases same : cell = target
    · simp only [response, FiniteProbRecord.singletonEvent, same, if_true, decide_true]
      exact SignedRatio.equiv_refl _
    · simp only [response, FiniteProbRecord.singletonEvent, same, if_false, decide_false, Bool.false_eq_true]
      exact SignedRatio.equiv_refl _
  have coefficients : (fun i : Fin cells.length => response (cells.getD i.val default)) =
      (fun i => if i = index then 1 else 0) := by
    funext i
    have same : cells.getD i.val default = target ↔ i = index :=
      (List.getD_inj i.isLt index.isLt distinct).trans ⟨Fin.ext, congrArg Fin.val⟩
    by_cases equal : i = index
    · simp only [response, if_pos (same.mpr equal), if_pos equal]
    · simp only [response, if_neg (fun h => equal (same.mp h)), if_neg equal]
  have mean := simplexGrid_integer_expectation cells default values simplex nonempty response
  rw [coefficients] at mean
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm indicator)
    (SignedRatio.equiv_trans mean (RationalLinear.dot_unit cells.length index values))

/-- Any actual finite law supplies valid auxiliary unit-interval coordinates. -/
def Distro.realUnitMass [DecidableEq A] (μ : Distro A) (cell : A) : UnitIntervalValue :=
  .ofQProb (μ.pmf cell) (by
    have bounded := (μ.probVal_bounds (FiniteProbRecord.singletonEvent cell)).2
    simpa only [QProb.LE, QProb.one, Nat.one_mul, Nat.mul_one] using bounded)

namespace PartialMomentProblem

/-- Auxiliary ideal laws have real coordinates but the same finite grid and
rational constraint rows as the actual rational inference problem. Domain
bounds are explicit, and normalization is included among the original rows.
This structure does not alter `Distro` or its executable rational solver. -/
structure RealCompatibleLaw (problem : PartialMomentProblem A) where
  mass : Fin problem.cells.length → UnitIntervalValue
  valid : RationalLinear.RealSatisfies problem.rows (fun i => (mass i).value)

/-- Every solution of the original real rows is admitted. In particular,
the unit-interval witnesses in the analytic interface are derived, not extra
assumptions on normalization, boundary coordinates or rank. -/
def RealCompatibleLaw.ofVector (problem : PartialMomentProblem A) (values : Fin problem.cells.length → ConstructiveReal)
    (valid : RationalLinear.RealSatisfies problem.rows values) : problem.RealCompatibleLaw where
  mass i :=
    let bounds := RationalLinear.real_simplex_bounds values (fun row member => valid row (List.mem_append_left _ member)) i
    ⟨values i, bounds.1, bounds.2⟩
  valid := valid

def RealCompatibleLaw.entropy {problem : PartialMomentProblem A} (law : problem.RealCompatibleLaw) : ConstructiveReal :=
  realEntropySum ((List.finRange problem.cells.length).map law.mass)

/-- Approximation returns an actual exactly feasible rational law, not
merely a vector with small constraint residuals. Every grid cell is retained. -/
def RealCompatibleLaw.approximate [DecidableEq A] {problem : PartialMomentProblem A}
    (law : problem.RealCompatibleLaw) (precision : PositiveRatio) :
    {rational : problem.CompatibleLaw // ∀ i, Within precision.toQProb (law.mass i).value
      (ofSignedRatio (rational.distro.pmf (problem.cells.getD i.val problem.default)).toSignedRatio)} := by
  let approximation := RationalLinear.approximateFeasible problem.rows (fun i => (law.mass i).value) law.valid precision
  let vector := approximation.val
  have valid := (problem.rows_iff vector).mp approximation.property.1
  let rational := problem.lawOfVector vector valid
  refine ⟨rational, ?_⟩
  intro i
  have mass := simplexGrid_pmf problem.cells problem.default vector valid.1 problem.nonempty problem.distinct i
  have massReal : Equiv (ofSignedRatio (vector i))
      (ofSignedRatio (rational.distro.pmf (problem.cells.getD i.val problem.default)).toSignedRatio) :=
    (ofSignedRatio_equiv_iff _ _).mpr (SignedRatio.equiv_symm mass)
  exact (within_congr (error := precision.toQProb) (equiv_refl (law.mass i).value) massReal).mp (approximation.property.2 i)

/-- The rational law interface embeds into the ideal feasible problem with
all its moment constraints, including redundant and boundary constraints. -/
def CompatibleLaw.toReal [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.CompatibleLaw) : problem.RealCompatibleLaw where
  mass i := law.distro.realUnitMass (problem.cells.getD i.val problem.default)
  valid := by
    have rational := (problem.rows_iff _).mpr (problem.vectorOfLaw law.distro law.support law.moments)
    intro row member
    exact (le_congr (RationalLinear.realDot_ofSignedRatio _ _ _) (equiv_refl _)).mpr
      ((ofSignedRatio_le_iff _ _).mpr (rational row member))

/-- Auxiliary entropy of an actual law agrees with the established exact
entropy on its distinct grid, with every null coordinate still present. -/
theorem CompatibleLaw.toReal_entropy [DecidableEq A] {problem : PartialMomentProblem A} (law : problem.CompatibleLaw) :
    Equiv law.toReal.entropy (law.distro.entropy problem.entropyGrid law.support).interpret := by
  let indices := List.finRange problem.cells.length
  have distributed := ExactLog.interpret_listSum (indices.map (fun i => Probability.entropyTerm
    (law.distro.pmf (problem.cells.getD i.val problem.default))))
  have mapped : Equiv law.toReal.entropy
      (listSum (indices.map (fun i => (Probability.entropyTerm (law.distro.pmf (problem.cells.getD i.val problem.default))).interpret))) := by
    simp only [RealCompatibleLaw.entropy, realEntropySum, List.map_map]
    exact listSum_map_congr indices _ _ (fun i _ => realEntropyTerm_ofQProb
      (law.distro.pmf (problem.cells.getD i.val problem.default)) (law.toReal.mass i).nonnegative (law.toReal.mass i).bounded)
  have original : indices.map (fun i => Probability.entropyTerm (law.distro.pmf (problem.cells.getD i.val problem.default))) =
      problem.cells.map (fun cell => Probability.entropyTerm (law.distro.pmf cell)) :=
    finRange_getD_map problem.cells problem.default (fun cell => Probability.entropyTerm (law.distro.pmf cell))
  simp only [List.map_map] at distributed
  have result := equiv_trans mapped (equiv_symm distributed)
  simpa only [Distro.entropy, entropyGrid, original] using result

end PartialMomentProblem
end Thesis.Probability.Distros
