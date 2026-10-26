import Thesis.Probability.ConstructiveRealMomentApproximation
import Thesis.Probability.ConstructiveRealEntropyVectorConcavity

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- Row evaluation is additive in the analytic assignment. Integer
coefficients may have either sign; no sign test on real coordinates occurs. -/
theorem realDot_add_values (variables : Nat) (coefficients : Fin variables → Int)
    (first second : Fin variables → ConstructiveReal) :
    Equiv (realDot variables coefficients (fun i => add (first i) (second i)))
      (add (realDot variables coefficients first) (realDot variables coefficients second)) := by
  induction variables with
  | zero => exact equiv_symm (zero_add zero)
  | succ variables ih =>
      exact equiv_trans (add_congr (mul_add _ _ _) (ih (fun i => coefficients i.castSucc)
        (fun i => first i.castSucc) (fun i => second i.castSucc))) (add_four _ _ _ _)

theorem realDot_mul_values (variables : Nat) (coefficients : Fin variables → Int)
    (values : Fin variables → ConstructiveReal) (factor : ConstructiveReal) :
    Equiv (realDot variables coefficients (fun i => mul (values i) factor))
      (mul (realDot variables coefficients values) factor) := by
  induction variables with
  | zero => exact equiv_symm (zero_mul factor)
  | succ variables ih =>
      exact equiv_trans (add_congr (equiv_symm (mul_assoc _ _ _))
        (ih (fun i => coefficients i.castSucc) (fun i => values i.castSucc))) (equiv_symm (add_mul _ _ _))

theorem realDot_midpoint (variables : Nat) (coefficients : Fin variables → Int)
    (first second : Fin variables → ConstructiveReal) :
    Equiv (realDot variables coefficients (fun i => midpoint (first i) (second i)))
      (midpoint (realDot variables coefficients first) (realDot variables coefficients second)) :=
  equiv_trans (realDot_mul_values variables coefficients _ _)
    (mul_congr (realDot_add_values variables coefficients first second) (equiv_refl _))

end Thesis.Probability.Distros.RationalLinear

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- All original closed linear rows are preserved by the midpoint.
Equalities, forced zeros and redundant rows require no separate cases. -/
def RealCompatibleLaw.midpoint {problem : PartialMomentProblem A} (first second : problem.RealCompatibleLaw) :
    problem.RealCompatibleLaw where
  mass i := (first.mass i).midpoint (second.mass i)
  valid row member := by
    have halfPositive : LE zero (ofSignedRatio (⟨1, 2, by decide⟩ : SignedRatio)) :=
      (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
    have compared := mul_le_mul_nonnegative_right halfPositive (add_le_add (first.valid row member) (second.valid row member))
    exact (le_congr (equiv_symm (RationalLinear.realDot_midpoint _ row.coefficients _ _))
      (midpoint_self (ofSignedRatio row.bound))).mp compared

/-- Sum of coordinate squared differences on the declared distinct grid. -/
def RealCompatibleLaw.squaredDistance {problem : PartialMomentProblem A} (first second : problem.RealCompatibleLaw) : ConstructiveReal :=
  listSum ((List.finRange problem.cells.length).map (fun i =>
    mul (sub (first.mass i).value (second.mass i).value) (sub (first.mass i).value (second.mass i).value)))

theorem RealCompatibleLaw.strong_midpoint {problem : PartialMomentProblem A} (first second : problem.RealCompatibleLaw) :
    LE (add (mul (add first.entropy second.entropy) (ofSignedRatio ⟨1, 2, by decide⟩))
      (mul (first.squaredDistance second) (ofSignedRatio ⟨1, 8, by decide⟩))) (first.midpoint second).entropy :=
  realEntropySum_strong_midpoint (List.finRange problem.cells.length) first.mass second.mass

theorem RealCompatibleLaw.coordinate_square_le_distance {problem : PartialMomentProblem A}
    (first second : problem.RealCompatibleLaw) (index : Fin problem.cells.length) :
    LE (mul (sub (first.mass index).value (second.mass index).value) (sub (first.mass index).value (second.mass index).value))
      (first.squaredDistance second) := by
  apply le_listSum_of_mem
  · intro value member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    exact square_nonnegative _
  · exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩

end Thesis.Probability.Distros.PartialMomentProblem
