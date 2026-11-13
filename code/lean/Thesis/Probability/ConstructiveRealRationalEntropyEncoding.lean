import Thesis.Probability.ConstructiveRealMomentRows
import Thesis.Probability.ConstructiveRealRationalConstraints
import Thesis.Probability.ConstructiveRealEntropyOptimizer

namespace Thesis.Probability.Distros
open ConstructiveReal

/-- An arbitrary finite rational polytope in the probability simplex.
Equalities are pairs of closed rows; redundancy and forced zeros are allowed. -/
structure RationalEntropyProblem (variables : Nat) where
  nonempty : 0 < variables
  rows : List (RationalLinear.RationalConstraint variables)

namespace RationalEntropyProblem

/-- Ideal coordinates are auxiliary analytic values, never new atom weights. -/
structure RealLaw (problem : RationalEntropyProblem variables) where
  mass : Fin variables → UnitIntervalValue
  normalized : Equiv (RationalLinear.realDot variables (fun _ => 1) (fun i => (mass i).value)) one
  valid : ∀ row ∈ problem.rows, row.RealHolds (fun i => (mass i).value)

def RealLaw.entropy {problem : RationalEntropyProblem variables} (law : problem.RealLaw) : ConstructiveReal :=
  realEntropySum ((List.finRange variables).map law.mass)

/-- The redundant lower endpoint is derived from the finite response. It
adds no feasibility assumption to the original one-sided inequality. -/
def rowMoment (row : RationalLinear.Inequality variables) : MomentInterval (Fin variables) :=
  ⟨row.coefficients, ⟨RationalLinear.coefficientLower variables row.coefficients, 1, by decide⟩, row.bound⟩

def encoded (problem : RationalEntropyProblem variables) : PartialMomentProblem (Fin variables) where
  cells := List.finRange variables
  default := ⟨0, problem.nonempty⟩
  nonempty := by simpa only [List.length_finRange] using problem.nonempty
  distinct := Probability.finRange_nodup variables
  intervals := problem.rows.map (fun row => rowMoment row.clear)

def gridIndex (problem : RationalEntropyProblem variables) (index : Fin problem.encoded.cells.length) : Fin variables :=
  Fin.cast List.length_finRange index

def lawIndex (problem : RationalEntropyProblem variables) (index : Fin variables) : Fin problem.encoded.cells.length :=
  Fin.cast List.length_finRange.symm index

theorem gridIndex_lawIndex (problem : RationalEntropyProblem variables) (index : Fin variables) :
    problem.gridIndex (problem.lawIndex index) = index := Fin.ext rfl

theorem lawIndex_gridIndex (problem : RationalEntropyProblem variables) (index : Fin problem.encoded.cells.length) :
    problem.lawIndex (problem.gridIndex index) = index := Fin.ext rfl

theorem grid_cell (problem : RationalEntropyProblem variables) (index : Fin problem.encoded.cells.length) :
    problem.encoded.cells.getD index.val problem.encoded.default = problem.gridIndex index := by
  exact (List.getElem_eq_getD problem.encoded.default).symm.trans (List.getElem_finRange index.isLt)

theorem row_coefficients (problem : RationalEntropyProblem variables) (row : RationalLinear.Inequality variables) :
    (rowMoment row).coefficients problem.encoded.cells problem.encoded.default =
      (fun i => row.coefficients (problem.gridIndex i)) := by
  funext i
  exact congrArg row.coefficients (problem.grid_cell i)

theorem dot_grid (problem : RationalEntropyProblem variables) (coefficients : Fin variables → Int)
    (values : Fin variables → ConstructiveReal) :
    Equiv (RationalLinear.realDot problem.encoded.cells.length (fun i => coefficients (problem.gridIndex i))
      (fun i => values (problem.gridIndex i))) (RationalLinear.realDot variables coefficients values) :=
  equiv_symm (RationalLinear.realDot_cast variables problem.encoded.cells.length List.length_finRange.symm coefficients values)

/-- The original rational rows encode as existing integer-response moments.
Only finite rational denominator clearing and finite dimension transport are
used; no independent rounding or analytic comparison is introduced. -/
def RealLaw.toEncoded {problem : RationalEntropyProblem variables} (law : problem.RealLaw) : problem.encoded.RealCompatibleLaw where
  mass i := law.mass (problem.gridIndex i)
  valid := by
    let values := fun i => (law.mass (problem.gridIndex i)).value
    have normalized : Equiv (RationalLinear.realDot problem.encoded.cells.length (fun _ => 1) values) one :=
      equiv_trans (problem.dot_grid (fun _ => 1) (fun i => (law.mass i).value)) law.normalized
    intro row member
    rcases List.mem_append.mp member with simplex | moment
    · exact RationalLinear.real_simplex_of_nonnegative values (fun i => (law.mass (problem.gridIndex i)).nonnegative) normalized row simplex
    · obtain ⟨constraint, listed, inside⟩ := List.mem_flatMap.mp moment
      obtain ⟨original, originalListed, same⟩ := List.mem_map.mp listed
      cases same
      apply (MomentInterval.real_rows_iff (rowMoment original.clear) problem.encoded.cells problem.encoded.default values).mpr ?_ row inside
      have dotSame : Equiv
          (RationalLinear.realDot problem.encoded.cells.length
            ((rowMoment original.clear).coefficients problem.encoded.cells problem.encoded.default) values)
          (RationalLinear.realDot variables original.clear.coefficients (fun i => (law.mass i).value)) := by
        rw [problem.row_coefficients original.clear]
        exact problem.dot_grid original.clear.coefficients (fun i => (law.mass i).value)
      have lower := RationalLinear.realDot_lower_normalized variables original.clear.coefficients
        (fun i => (law.mass i).value) (fun i => (law.mass i).nonnegative) law.normalized
      have upper := (original.clear_real_iff (fun i => (law.mass i).value)).mpr (law.valid original originalListed)
      exact ⟨(le_congr (equiv_refl _) dotSame).mpr lower, (le_congr dotSame (equiv_refl _)).mpr upper⟩

end RationalEntropyProblem
end Thesis.Probability.Distros
