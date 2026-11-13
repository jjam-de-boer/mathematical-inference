import Thesis.Probability.Distros.RationalLinearProjection
import Thesis.Probability.Distros.MomentTableCheck

namespace Thesis.Probability.Distros.RationalLinear

theorem extend_restrict (values : Fin (variables + 1) → SignedRatio) :
    extend (fun i => values i.castSucc) (values (Fin.last variables)) = values := by
  funext i
  by_cases earlier : i.val < variables
  · let old : Fin variables := ⟨i.val, earlier⟩
    have same : old.castSucc = i := Fin.ext rfl
    rw [← same, extend_castSucc]
  · have same : i = Fin.last variables := Fin.ext (by simp only [Fin.val_last]; have bound := i.isLt; omega)
    rw [same, extend_last]

/-- A finite elimination trace ends in an actual contradictory constant
row. This is checked data, not an oracle declaring the system infeasible. -/
inductive Infeasibility : (variables : Nat) → List (Inequality variables) → Type where
  | constant (rows : List (Inequality 0)) (row : Inequality 0) (member : row ∈ rows) (negative : row.bound.num < 0) :
      Infeasibility 0 rows
  | projected (rows : List (Inequality (variables + 1))) (previous : Infeasibility variables (project rows)) :
      Infeasibility (variables + 1) rows

theorem Infeasibility.not_exists (certificate : Infeasibility variables rows) :
    ¬ ∃ values : Fin variables → SignedRatio, Satisfies rows values := by
  induction certificate with
  | constant rows row member negative =>
      rintro ⟨values, valid⟩
      have bound : SignedRatio.LE SignedRatio.zero row.bound := valid row member
      have nonnegative := (SignedRatio.nonnegative_congr (SignedRatio.sub_zero row.bound)).mp bound
      change 0 ≤ row.bound.num at nonnegative
      omega
  | projected rows previous ih =>
      rintro ⟨values, valid⟩
      apply ih
      refine ⟨fun i => values i.castSucc, project_sound rows _ (values (Fin.last _)) ?_⟩
      simpa only [extend_restrict] using valid

inductive SolveResult (variables : Nat) (rows : List (Inequality variables)) where
  | feasible (values : Fin variables → SignedRatio) (valid : Satisfies rows values)
  | infeasible (certificate : Infeasibility variables rows)

/-- Complete constructive rational linear feasibility. Elimination uses
integer row combinations; back-substitution uses computed rational endpoints.
The number of variables decreases at every recursive call. -/
def solve : (variables : Nat) → (rows : List (Inequality variables)) → SolveResult variables rows
  | 0, rows =>
      match checkFiniteMasses rows (fun row => row.bound) with
      | .negative row member negative => .infeasible (.constant rows row member negative)
      | .nonnegative nonnegative => .feasible (fun i => Fin.elim0 i) (by
          intro row member
          exact (SignedRatio.nonnegative_congr (SignedRatio.sub_zero row.bound)).mpr (nonnegative row member))
  | variables + 1, rows =>
      match solve variables (project rows) with
      | .infeasible certificate => .infeasible (.projected rows certificate)
      | .feasible values valid =>
          let last := lift rows values valid
          .feasible (extend values last.val) last.property

theorem solve_success_iff (variables : Nat) (rows : List (Inequality variables)) :
    (match solve variables rows with | .feasible _ _ => True | .infeasible _ => False) ↔
      ∃ values : Fin variables → SignedRatio, Satisfies rows values := by
  cases result : solve variables rows with
  | feasible values valid =>
      constructor
      · intro _; exact ⟨values, valid⟩
      · intro _; trivial
  | infeasible certificate =>
      constructor
      · intro impossible; exact False.elim impossible
      · intro realizable; exact False.elim (certificate.not_exists realizable)

end Thesis.Probability.Distros.RationalLinear
